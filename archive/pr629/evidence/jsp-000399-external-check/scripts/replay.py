"""Prospective native-host replay of the recorded JSP399 external check.

Prepared and syntax/help checked, but not executed end-to-end during packaging.
Uses existing Lean/Rust tools; never installs a toolchain or Mathlib.
Apache-2.0. Gott-L-directed project, with Codex implementation assistance.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import threading
import time

PACKAGE = Path(__file__).resolve().parent.parent
CAP = 100 * 1024**2


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def dump(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + "\n", "utf-8")


def tool(value):
    found = shutil.which(value)
    path = Path(found or value).resolve()
    if not path.is_file():
        raise RuntimeError(f"Executable not found: {value}")
    return path


def run(command, cwd, env, prefix, timeout=600):
    start = time.monotonic()
    with Path(str(prefix) + ".stdout.txt").open("xb") as out, Path(str(prefix) + ".stderr.txt").open("xb") as err:
        process = subprocess.run(list(map(str, command)), cwd=cwd, env=env,
                                 stdout=out, stderr=err, timeout=timeout)
    return {"command": list(map(str, command)), "exit_code": process.returncode,
            "seconds": round(time.monotonic()-start, 3),
            "stdout_sha256": sha(Path(str(prefix) + ".stdout.txt")),
            "stderr_sha256": sha(Path(str(prefix) + ".stderr.txt"))}


def export_bounded(command, cwd, env, output, errors):
    failure = []
    with errors.open("xb") as err:
        process = subprocess.Popen(list(map(str, command)), cwd=cwd, env=env,
                                   stdout=subprocess.PIPE, stderr=err)

        def pump():
            size = 0
            try:
                with output.open("xb") as out:
                    while chunk := process.stdout.read(65536):
                        if size + len(chunk) > CAP:
                            raise RuntimeError("Export exceeded 100 MiB")
                        out.write(chunk)
                        size += len(chunk)
            except Exception as exc:
                failure.append(str(exc))
                process.kill()

        thread = threading.Thread(target=pump, daemon=True)
        thread.start()
        try:
            code = process.wait(timeout=600)
        except subprocess.TimeoutExpired:
            process.kill()
            process.wait()
            failure.append("Export timeout")
            code = -1
        thread.join(timeout=30)
        if code or thread.is_alive() or failure:
            raise RuntimeError(f"Export failed: code={code}; errors={failure}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", required=True)
    parser.add_argument("--cargo", required=True)
    parser.add_argument("--rustc", help="Defaults to rustc beside the specified Cargo executable")
    parser.add_argument("--nanoda-src", type=Path, required=True)
    parser.add_argument("--proof-dir", type=Path, default=PACKAGE.parent / "jsp-000399-parametric-27")
    parser.add_argument("--work-dir", type=Path, required=True)
    args = parser.parse_args()
    lean, cargo = tool(args.lean), tool(args.cargo)
    rustc = tool(args.rustc or str(cargo.parent / ("rustc.exe" if os.name == "nt" else "rustc")))
    lean_version = subprocess.check_output([str(lean), "--version"], text=True)
    rust_version = subprocess.check_output([str(rustc), "--version", "--verbose"], text=True)
    if "version 4.19.0," not in lean_version or not rust_version.startswith("rustc 1.93.0 "):
        raise RuntimeError("This replay requires Lean 4.19.0 and Rust 1.93.0")
    expected_export = json.loads((PACKAGE / "records/export-result.redacted.json").read_text("utf-8"))
    checker_manifest = json.loads((PACKAGE / "checker-source-manifest.json").read_text("utf-8"))
    proof_dir, checker_source = args.proof_dir.resolve(), args.nanoda_src.resolve()
    for name, expected in expected_export["published_sources"].items():
        if sha(proof_dir / name) != expected["sha256"]:
            raise RuntimeError(f"Proof source hash mismatch: {name}")
    for expected in checker_manifest["files"]:
        if sha(checker_source / expected["path"]) != expected["sha256"]:
            raise RuntimeError("Pinned checker source mismatch: " + expected["path"])
    work = args.work_dir.resolve()
    if work.exists() and any(work.iterdir()):
        raise RuntimeError("Use a new or empty work directory")
    work.mkdir(parents=True, exist_ok=True)
    proof, exporter, logs = work / "proof", work / "exporter", work / "logs"
    for directory in [proof, exporter, logs]:
        directory.mkdir()
    for name in expected_export["published_sources"]:
        shutil.copyfile(proof_dir / name, proof / name)
    for name in ["Export.lean", "Main.lean"]:
        shutil.copyfile(PACKAGE / "exporter" / name, exporter / name)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(proof), str(exporter)])
    receipt = {"replay_driver_sha256": sha(Path(__file__)), "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
               "lean_version": lean_version, "rust_version": rust_version,
               "independent_operator": False, "official_verification": False,
               "checker_run": False, "all_checks_passed": False, "compile_results": []}
    try:
        for module, directory in [("Jsp399TripleCore", proof), ("Jsp399Witness", proof),
                                  ("EncodedCoeffCertificate", proof), ("Jsp399Parametric", proof),
                                  ("Export", exporter), ("Main", exporter)]:
            command = [lean, "--trust=0", "-s", "65536", "-j", "1", "-DElab.async=false",
                       "-DwarningAsError=true", "-o", module + ".olean", module + ".lean"]
            result = run(command, directory, env, logs / ("compile-" + module))
            receipt["compile_results"].append(result)
            if result["exit_code"]:
                raise RuntimeError(f"Fresh compilation failed: {module}")
        env.update(CARGO_HOME=str(work / "cargo-home"), CARGO_TARGET_DIR=str(work / "cargo-target"),
                   CARGO_INCREMENTAL="0", RUSTC=str(rustc))
        build = run([cargo, "build", "--release", "--locked", "--bin", "nanoda_bin", "-j", "1"],
                    checker_source, env, logs / "checker-build")
        receipt["checker_build"] = build
        if build["exit_code"]:
            raise RuntimeError("Checker build failed")
        binary = work / "cargo-target/release" / ("nanoda_bin.exe" if os.name == "nt" else "nanoda_bin")
        receipt["checker_binary_sha256"] = sha(binary)
        roots = expected_export["roots_requested"]
        output = work / "export.ndjson"
        export_bounded([lean, "--trust=0", "-s", "65536", "-j", "1", "-DElab.async=false", "--run",
                        exporter / "Main.lean", "Jsp399Parametric", "--", "--"] + roots,
                       exporter, env, output, logs / "export.stderr.txt")
        spec = importlib.util.spec_from_file_location("recorded_runner", PACKAGE / "scripts/run_nanoda.recorded.py")
        recorded = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(recorded)
        inventory = recorded.inspect_export(output, roots)
        receipt["input"] = inventory
        control = "JSP399Parametric.vector_triple_sums_perm"
        receipt["negative_control_target"] = control
        receipt["runs"] = {}
        template = json.loads((PACKAGE / "configs/full-lowered.valid.redacted.json").read_text("utf-8"))
        for kind in ["valid", "wrong-proof", "unpermitted-axiom"]:
            data = output
            if kind != "valid":
                data = work / (kind + ".ndjson")
                diff = recorded.mutate_export(output, data, inventory["targets"][control],
                                              inventory["wrong_proof_literal"], kind)
                receipt.setdefault("mutations", {})[kind] = diff
            pp = logs / (kind + ".declarations.txt")
            pp.touch(exist_ok=False)
            config = dict(template, export_file_path=str(data), pp_output_path=str(pp), pp_declars=roots)
            config_path = work / (kind + ".config.json")
            dump(config_path, config)
            result = run([binary, config_path], work, env, logs / kind)
            stdout = (logs / (kind + ".stdout.txt")).read_text("utf-8")
            stderr = (logs / (kind + ".stderr.txt")).read_text("utf-8")
            if kind == "valid":
                receipt["checker_run"] = True
                rendered = pp.read_text("utf-8")
                names_ok = all(re.search(r"\btheorem\s+" + re.escape(name) + r"(?=\s|:|\.\{)", rendered) for name in roots)
                banner = f"Checked {inventory['declaration_count']} declarations with no errors"
                accepted = result["exit_code"] == 0 and not stderr.strip() and stdout.strip().endswith(banner) and names_ok
                accepted &= "pretty printer error" not in (stdout + stderr).lower()
            elif kind == "wrong-proof":
                accepted = result["exit_code"] not in [0, 124, 137] and "assertion failed: self.def_eq(u, v)" in stderr
            else:
                accepted = result["exit_code"] not in [0, 124, 137] and f'export file declares unpermitted axiom "{control}"' in stderr
            result["expected_outcome"] = bool(accepted)
            result["config_sha256"] = sha(config_path)
            receipt["runs"][kind] = result
            if not accepted:
                raise RuntimeError("Unexpected checker outcome: " + kind)
        if sha(output) != inventory["sha256"]:
            raise RuntimeError("Original input changed")
        receipt["all_checks_passed"] = True
    finally:
        receipt["finished_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        dump(work / "replay-result.json", receipt)
    print(json.dumps({"all_checks_passed": True, "receipt": str(work / "replay-result.json")}, indent=2))


if __name__ == "__main__":
    main()
