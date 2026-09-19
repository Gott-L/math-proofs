"""Bounded, explicit-target Nanoda runner for the Lean 4.19 pilot.

Run from Windows Python; the checker executes in the existing WSL distribution.
No compilation, installation, source alteration, or publication is performed.
"""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time


ROOT = Path(__file__).resolve().parent
CHECKER_COMMIT = "4c544ed4099c8227f07d5de77ad1e69fb0740a27"
LEAN_COMMIT = "6caaee842e9495688c1567e78c0e68dbb96942aa"
ALLOWED_AXIOMS = ["propext", "Classical.choice", "Quot.sound"]
COPY_LIMIT = 100 * 1024**2
TOTAL_LIMIT = 3 * 1024**3
RESERVE_BYTES = 16 * 1024**2
DECL_KINDS = ("axiom", "def", "thm", "opaque", "quot")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def tree_bytes(path: Path) -> int:
    """Do not traverse junctions/symlinks into already-accounted dependencies."""
    total = 0
    for base, dirs, files in os.walk(path, followlinks=False):
        dirs[:] = [name for name in dirs if not is_reparse(Path(base) / name)]
        for name in files:
            item = Path(base) / name
            if not is_reparse(item):
                total += item.stat().st_size
    return total


def is_reparse(path: Path) -> bool:
    info = path.lstat()
    return path.is_symlink() or bool(getattr(info, "st_file_attributes", 0) & 0x400)


def linux_path(path: Path) -> str:
    path = path.resolve()
    if os.name != "nt":
        return str(path)
    if not re.fullmatch(r"[A-Za-z]:", path.drive):
        raise ValueError("Only local Windows drive paths are supported by this WSL runner")
    return "/mnt/" + path.drive[0].lower() + "/" + "/".join(path.parts[1:])


def write_json(path: Path, value: object) -> None:
    with path.open("x", encoding="utf-8", newline="\n") as stream:
        json.dump(value, stream, indent=2, ensure_ascii=False)
        stream.write("\n")


def inspect_export(path: Path, targets: list[str]) -> dict:
    """Inventory records, resolving names and requiring genuine proof records.

    This preflight is not a replacement for Nanoda's expression/type checks.
    It retains name and expression-index tables, not all expression bodies.
    """
    names = {0: ""}
    exprs: set[int] = set()
    declarations: dict[str, str] = {}
    roots = {}
    axioms = []
    nat_candidates = []
    meta = None
    string_literals = 0
    rows = 0
    digest = hashlib.sha256()

    def declar(kind: str, payload: dict, line: int) -> None:
        name = names[payload["name"]]
        if name in declarations:
            raise ValueError(f"Duplicate declaration {name!r} at line {line}")
        declarations[name] = kind
        if kind == "axiom":
            axioms.append(name)
        if payload.get("isUnsafe") or payload.get("safety") in ("unsafe", "partial"):
            raise ValueError(f"Unsafe/partial declaration {name!r}")
        if name in targets:
            if kind != "thm":
                raise ValueError(f"Target {name!r} has kind {kind!r}, expected thm")
            for key in ("type", "value"):
                if type(payload.get(key)) is not int or payload[key] not in exprs:
                    raise ValueError(f"Target {name!r} has invalid {key} expression reference")
            if not isinstance(payload.get("levelParams"), list):
                raise ValueError(f"Target {name!r} has no universe-parameter list")
            roots[name] = {"line": line, "kind": kind, "record": payload}

    with path.open("rb") as stream:
        for line, raw in enumerate(stream, 1):
            rows = line
            digest.update(raw)
            row = json.loads(raw)
            if not isinstance(row, dict):
                raise ValueError(f"Expected JSON object at line {line}")
            if line == 1:
                if set(row) != {"meta"}:
                    raise ValueError("The first record must be metadata")
                meta = row["meta"]
                if meta.get("lean", {}).get("version") != "4.19.0":
                    raise ValueError("Only genuine Lean 4.19.0 exports are accepted")
                if meta.get("lean", {}).get("githash") != LEAN_COMMIT:
                    raise ValueError("Unexpected Lean compiler revision")
                if meta.get("format", {}).get("version") != "3.1.0":
                    raise ValueError("Export format must be exactly 3.1.0")
                continue
            if "meta" in row:
                raise ValueError("Repeated metadata")
            if "in" in row:
                index = row["in"]
                if index in names:
                    raise ValueError(f"Duplicate name index {index}")
                part = row.get("str", row.get("num"))
                prefix = names[part["pre"]]
                suffix = part["str"] if "str" in row else str(part["i"])
                names[index] = prefix + ("." if prefix else "") + suffix
            if "ie" in row:
                index = row["ie"]
                if type(index) is not int or index in exprs:
                    raise ValueError(f"Invalid or duplicate expression index at line {line}")
                exprs.add(index)
                if "natVal" in row and not nat_candidates:
                    if not str(row["natVal"]).isdigit():
                        raise ValueError("Invalid natural literal")
                    nat_candidates.append({"index": index, "value": row["natVal"], "line": line})
                if "strVal" in row:
                    string_literals += 1
            for kind in DECL_KINDS:
                if kind in row:
                    declar(kind, row[kind], line)
            if "inductive" in row:
                for field, kind in (("types", "inductive"), ("ctors", "constructor"), ("recs", "recursor")):
                    for payload in row["inductive"][field]:
                        declar(kind, payload, line)
    if meta is None:
        raise ValueError("Empty export")
    if string_literals:
        raise ValueError(f"Unsupported Lean-version string literals present: {string_literals}")
    if set(axioms) - set(ALLOWED_AXIOMS):
        raise ValueError(f"Unpermitted input axioms: {sorted(set(axioms) - set(ALLOWED_AXIOMS))}")
    missing = set(targets) - set(roots)
    if missing:
        raise ValueError(f"Targets missing from export: {sorted(missing)}")
    return {
        "path": str(path), "bytes": path.stat().st_size, "sha256": digest.hexdigest(),
        "metadata": meta, "rows": rows, "declaration_count": len(declarations),
        "expression_count": len(exprs), "string_literal_records": string_literals,
        "axioms": axioms, "targets": roots,
        "wrong_proof_literal": nat_candidates[0] if nat_candidates else None,
    }


def make_config(input_path: Path, pp_path: Path, targets: list[str]) -> dict:
    return {
        "export_file_path": linux_path(input_path), "use_stdin": False,
        "permitted_axioms": ALLOWED_AXIOMS,
        "unpermitted_axiom_hard_error": True, "unsafe_permit_all_axioms": False,
        "unknown_pp_declar_hard_error": True, "num_threads": 1,
        "nat_extension": True, "string_extension": False,
        "pp_declars": targets, "pp_output_path": linux_path(pp_path),
        "pp_to_stdout": False,
        "pp_options": {"all": False, "explicit": True, "universes": True,
                       "notation": False, "proofs": False, "indent": 2,
                       "width": 160, "declar_sep": "\n\n"},
        "print_success_message": True, "print_axioms": True,
    }


def mutate_export(source: Path, dest: Path, root: dict, literal: dict | None, kind: str) -> dict:
    old = root["record"]
    if kind == "wrong-proof":
        if literal is None or literal["line"] >= root["line"]:
            raise ValueError("No existing earlier Nat literal available for wrong-proof control")
        new = {**old, "value": literal["index"]}
        row = {"thm": new}
        changed_fields = ["thm.value"]
    else:
        new = {key: old[key] for key in ("name", "levelParams", "type")}
        new["isUnsafe"] = False
        row = {"axiom": new}
        changed_fields = ["declaration_kind", "proof_value_removed", "isUnsafe=false"]
    assert new["name"] == old["name"] and new["type"] == old["type"]
    assert new["levelParams"] == old["levelParams"]
    digest = hashlib.sha256()
    changed = 0
    with source.open("rb") as src, dest.open("xb") as out:
        for line, raw in enumerate(src, 1):
            if line == root["line"]:
                if json.loads(raw) != {"thm": old}:
                    raise ValueError("Original target record changed since preflight")
                raw = (json.dumps(row, separators=(",", ":"), ensure_ascii=False) + "\n").encode("utf-8")
                changed += 1
            out.write(raw)
            digest.update(raw)
    if changed != 1:
        raise ValueError("Control did not change exactly one record")
    return {"path": str(dest), "bytes": dest.stat().st_size, "sha256": digest.hexdigest(),
            "changed_record_count": changed, "line": root["line"],
            "changed_fields": changed_fields, "old_record": {"thm": old}, "new_record": row,
            "name_type_universes_preserved": True}


def execute(binary: Path, cfg_path: Path, label: str, prefix: Path, timeout: int, distro: str) -> dict:
    out_path = Path(str(prefix) + f".{label}.stdout.txt")
    err_path = Path(str(prefix) + f".{label}.stderr.txt")
    command = ["timeout", "--signal=TERM", "--kill-after=5s", f"{timeout}s",
               linux_path(binary), linux_path(cfg_path)]
    if os.name == "nt":
        command = ["wsl.exe", "-d", distro, "--exec"] + command
    start = time.monotonic()
    timed_out = False
    with out_path.open("xb") as out, err_path.open("xb") as err:
        try:
            result = subprocess.run(command, stdout=out, stderr=err, timeout=timeout + 30)
            code = result.returncode
            timed_out = code in (124, 137)
        except subprocess.TimeoutExpired:
            code, timed_out = None, True
    stdout = out_path.read_text(encoding="utf-8", errors="replace")
    stderr = err_path.read_text(encoding="utf-8", errors="replace")
    return {"command": command, "exit_code": code, "timed_out": timed_out,
            "seconds": round(time.monotonic() - start, 3),
            "stdout_path": str(out_path), "stderr_path": str(err_path),
            "stdout_sha256": sha256(out_path), "stderr_sha256": sha256(err_path),
            "stdout": stdout, "stderr": stderr}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--target", action="append", required=True, help="Exact theorem name; repeatable")
    parser.add_argument("--control-target", help="Target for both negative controls; defaults to first target")
    parser.add_argument("--output-prefix", type=Path, required=True)
    parser.add_argument("--binary", type=Path, default=ROOT / "cargo-target/release/nanoda_bin")
    parser.add_argument("--build-receipt", type=Path, default=ROOT / "checker-build-receipt.json")
    parser.add_argument("--export-receipt", type=Path,
                        help="Required source/proof export provenance for nonsynthetic runs")
    parser.add_argument("--distribution", default="Ubuntu-24.04")
    parser.add_argument("--timeout-seconds", type=int, default=600)
    parser.add_argument("--accounted-external-bytes", type=int, default=int(1.868 * 1024**3),
                        help="Already allocated shared environment outside this pilot; conservative default")
    parser.add_argument("--scope", choices=("synthetic", "enumeration-lemmas", "submitted-endpoints"),
                        default="synthetic", help="Explicit label only; provenance must also be reviewed")
    parser.add_argument("--preflight-only", action="store_true")
    args = parser.parse_args()
    if len(set(args.target)) != len(args.target):
        parser.error("Duplicate --target")
    control_target = args.control_target or args.target[0]
    if control_target not in args.target:
        parser.error("--control-target must be one of the required --target names")
    if args.scope != "synthetic" and args.export_receipt is None:
        parser.error("Nonsynthetic scope requires --export-receipt")
    if not 1 <= args.timeout_seconds <= 600 or args.accounted_external_bytes < 0:
        parser.error("Timeout must be 1..600 seconds and external storage must be nonnegative")
    source, prefix = args.input.resolve(), args.output_prefix.resolve()
    if not prefix.is_relative_to(ROOT):
        parser.error("Output prefix must remain inside checker-pilot")
    prefix.parent.mkdir(parents=True, exist_ok=True)
    receipt_path = Path(str(prefix) + ".result.json")
    if any(prefix.parent.glob(prefix.name + ".*")):
        parser.error("Output prefix already has artifacts; choose a fresh prefix")
    receipt = {
        "started_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "runner_sha256": sha256(Path(__file__)), "scope": args.scope,
        "targets": args.target, "negative_control_target": control_target,
        "checker_commit": CHECKER_COMMIT, "independent_implementation": True,
        "independent_operator": False, "official_verification": False,
        "network_isolation": False, "checker_run": False, "all_checks_passed": False,
        "submitted_endpoint_pass": False, "preflight_only": args.preflight_only,
        "limits": {"total_bytes": TOTAL_LIMIT, "negative_control_copy_limit_bytes": COPY_LIMIT,
                   "accounted_external_bytes": args.accounted_external_bytes,
                   "timeout_seconds_per_run": args.timeout_seconds},
    }
    try:
        used = tree_bytes(ROOT) + args.accounted_external_bytes
        receipt["storage_bytes_before"] = used
        if used + RESERVE_BYTES > TOTAL_LIMIT:
            raise RuntimeError("Cumulative storage is too close to the 3 GiB ceiling")
        inventory = inspect_export(source, args.target)
        receipt["input"] = inventory
        if args.export_receipt is not None:
            exported = json.loads(args.export_receipt.read_text(encoding="utf-8"))
            if (exported.get("export_gate_passed") is not True
                    or exported.get("export_sha256") != inventory["sha256"]
                    or not set(args.target) <= set(exported.get("roots_requested", []))):
                raise ValueError("Source export receipt does not cover this input and its exact targets")
            source_roots = {item["name"]: item for item in exported["roots"]}
            for name in args.target:
                source_root = source_roots[name]
                actual = inventory["targets"][name]
                if (source_root["kind"] != "thm"
                        or source_root["type_reference"] != actual["record"]["type"]
                        or source_root["value_reference"] != actual["record"]["value"]):
                    raise ValueError(f"Source export target mismatch: {name}")
            receipt["export_provenance"] = {
                "receipt_path": str(args.export_receipt.resolve()),
                "receipt_sha256": sha256(args.export_receipt),
                "proof_repository": exported.get("proof_repository"),
                "proof_commit": exported.get("proof_commit"),
                "proof_packet": exported.get("proof_packet"),
                "stage": exported.get("stage"),
                "source_to_export_record_matched": True,
            }
        receipt["preflight_passed"] = True
        if args.preflight_only:
            receipt["status"] = "preflight-only; no checker executed"
            return 0
        binary = args.binary.resolve()
        build = json.loads(args.build_receipt.read_text(encoding="utf-8"))
        binary_hash = sha256(binary)
        if (build.get("commit") != CHECKER_COMMIT or build.get("exit_code") != 0
                or build.get("source_unchanged") is not True
                or build.get("binary_sha256") != binary_hash):
            raise ValueError("Checker binary does not match a successful pinned build receipt")
        receipt["checker_binary"] = {"path": str(binary), "sha256": binary_hash,
                                     "bytes": binary.stat().st_size}
        receipt["build_receipt_sha256"] = sha256(args.build_receipt)
        receipt["runs"] = {}
        pp = Path(str(prefix) + ".valid.declarations.txt")
        cfg = Path(str(prefix) + ".valid.config.json")
        # The pinned checker opens this file without create(true).
        pp.touch(exist_ok=False)
        write_json(cfg, make_config(source, pp, args.target))
        valid = execute(binary, cfg, "valid", prefix, args.timeout_seconds, args.distribution)
        receipt["checker_run"] = True
        valid["config_sha256"] = sha256(cfg)
        rendered = pp.read_text(encoding="utf-8") if pp.exists() else ""
        if pp.exists():
            valid["declarations_sha256"] = sha256(pp)
        valid["target_declarations_printed"] = {
            name: bool(re.search(r"\btheorem\s+" + re.escape(name) + r"(?=\s|:|\.\{)", rendered))
            for name in args.target
        }
        match = re.fullmatch(r"Checked (\d+) declarations with no errors", valid["stdout"].strip().splitlines()[-1] if valid["stdout"].strip() else "")
        valid["checker_declaration_count"] = int(match[1]) if match else None
        valid["accepted"] = bool(
            valid["exit_code"] == 0 and not valid["timed_out"] and match
            and int(match[1]) == inventory["declaration_count"]
            and all(valid["target_declarations_printed"].values())
            and "pretty printer error" not in (valid["stdout"] + valid["stderr"]).lower()
            and not valid["stderr"].strip()
        )
        receipt["runs"]["valid"] = valid
        if not valid["accepted"]:
            raise RuntimeError("Baseline checker acceptance or exact-target display check failed")
        projected = tree_bytes(ROOT) + args.accounted_external_bytes + 2 * inventory["bytes"] + RESERVE_BYTES
        if inventory["bytes"] > COPY_LIMIT or projected > TOTAL_LIMIT:
            receipt["negative_controls"] = {"status": "not run: bounded copy/storage limit",
                                            "projected_total_bytes": projected}
            raise RuntimeError("Baseline passed, but negative controls exceed the recorded resource limit")
        if inventory["wrong_proof_literal"] is None:
            raise ValueError("No existing Nat literal for the required wrong-proof control")
        receipt["negative_controls"] = {}
        for kind in ("wrong-proof", "unpermitted-axiom"):
            if sha256(source) != inventory["sha256"]:
                raise ValueError("Original successful input changed")
            bad = Path(str(prefix) + f".{kind}.ndjson")
            diff = mutate_export(source, bad, inventory["targets"][control_target],
                                 inventory["wrong_proof_literal"], kind)
            bad_pp = Path(str(prefix) + f".{kind}.declarations.txt")
            bad_cfg = Path(str(prefix) + f".{kind}.config.json")
            bad_pp.touch(exist_ok=False)
            write_json(bad_cfg, make_config(bad, bad_pp, args.target))
            result = execute(binary, bad_cfg, kind, prefix, args.timeout_seconds, args.distribution)
            result["config_sha256"] = sha256(bad_cfg)
            combined = result["stdout"] + result["stderr"]
            if kind == "wrong-proof":
                expected = "assertion failed: self.def_eq(u, v)" in combined
            else:
                expected = f'export file declares unpermitted axiom "{control_target}"' in combined
            unrelated = any(fragment in combined.lower() for fragment in
                            ("pp_declars were not found", "pretty printer error", "no such file", "failed to open", "invalid type:", "expected value at line"))
            result["expected_failure"] = bool(result["exit_code"] not in (None, 0, 124, 137)
                                               and not result["timed_out"] and expected and not unrelated)
            receipt["negative_controls"][kind] = {"mutation": diff, "run": result}
            if not result["expected_failure"]:
                raise RuntimeError(f"{kind} did not fail for its required reason")
        if sha256(source) != inventory["sha256"] or sha256(binary) != binary_hash:
            raise ValueError("Successful input or checker binary changed during the run")
        receipt["all_checks_passed"] = True
        receipt["submitted_endpoint_pass"] = args.scope == "submitted-endpoints"
        receipt["status"] = "baseline and both targeted negative controls passed"
        return 0
    except Exception as error:
        receipt["status"] = "incomplete or failed"
        receipt["error"] = f"{type(error).__name__}: {error}"
        return 1
    finally:
        receipt["finished_utc"] = dt.datetime.now(dt.timezone.utc).isoformat()
        receipt["storage_bytes_after"] = tree_bytes(ROOT) + args.accounted_external_bytes
        write_json(receipt_path, receipt)
        print(json.dumps({"receipt": str(receipt_path), "status": receipt["status"],
                          "all_checks_passed": receipt["all_checks_passed"],
                          "submitted_endpoint_pass": receipt["submitted_endpoint_pass"]}, indent=2))


if __name__ == "__main__":
    sys.exit(main())
