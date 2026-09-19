"""Check the seven actual literals against their Lean 4.19 constructor forms."""
import datetime
import difflib
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    lean = str(Path(sys.argv[1]).resolve())
    original = ROOT.parent / "exports-full/export.ndjson"
    assert sha(original) == "bf9c742f6def570ef5ccb51e6886d712e2d97db9bac21806d329a4f6537bafd5"
    strings = []
    with original.open(encoding="utf-8") as stream:
        for line_no, text in enumerate(stream, 1):
            obj = json.loads(text)
            if "strVal" in obj:
                strings.append({"line": line_no, "expression_reference": obj["ie"],
                                "text": obj["strVal"], "codepoints": list(map(ord, obj["strVal"]))})
    assert len(strings) == 7
    lines = ["import Export", "", "namespace StringLoweringCases", ""]
    for i, item in enumerate(strings):
        name = f"StringLoweringCases.literal_{i}"
        item["equality_theorem"] = name
        literal = json.dumps(item["text"], ensure_ascii=False)
        chars = ", ".join("Char.ofNat " + str(n) for n in item["codepoints"])
        lines += [f"theorem literal_{i} : ({literal} : String) = String.mk [{chars}] := rfl",
                  f"#print axioms literal_{i}", ""]
    lines += ["end StringLoweringCases", ""]
    source = ROOT / "StringLoweringCases.lean"
    source.write_text("\n".join(lines), "utf-8", newline="\n")
    patch = "".join(difflib.unified_diff(
        (ROOT / "before-string-lowering/Export.lean").read_text("utf-8").splitlines(True),
        (ROOT / "Export.lean").read_text("utf-8").splitlines(True),
        fromfile="before-string-lowering/Export.lean", tofile="string-lowered/Export.lean"))
    (ROOT / "string-lowering.patch").write_text(patch, "utf-8", newline="\n")
    env = os.environ.copy()
    env["LEAN_PATH"] = str(ROOT)
    compile_results = []
    for module in ["Export", "Main", "StringLoweringCases"]:
        args = ["--trust=0", "-DwarningAsError=true", "-o", module + ".olean", module + ".lean"]
        proc = subprocess.run([lean] + args, cwd=ROOT, env=env, capture_output=True, timeout=120)
        log = ROOT / (module + ".lowering.compile.log")
        log.write_bytes(proc.stdout + proc.stderr)
        if proc.returncode:
            raise RuntimeError(f"Compilation failed: {module}; see {log.name}")
        compile_results.append({"module": module, "arguments": args, "exit_code": proc.returncode,
                                "log": log.name, "log_sha256": sha(log)})
        if module == "StringLoweringCases":
            output = proc.stdout.decode("utf-8")
            for item in strings:
                expected = "'" + item["equality_theorem"] + "' does not depend on any axioms"
                if expected not in output:
                    raise RuntimeError("Missing axiom-free equality audit: " + item["equality_theorem"])
    baseline = json.loads((ROOT / "before-string-lowering/gate-result.json").read_text("utf-8"))
    assert sha(Path(lean)) == baseline["lean_binary_sha256"]
    record = {
        "checked_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "upstream_commit": baseline["upstream_commit"],
        "lean_binary_sha256": sha(Path(lean)),
        "lean_version_output": baseline["lean_version_output"],
        "exporter_name": "lean4export-lean4.19-string-lowered",
        "exporter_version": "3.1.0+lean4.19.string-lowered",
        "format_version": "3.1.0",
        "previous_gate_sha256": sha(ROOT / "before-string-lowering/gate-result.json"),
        "original_export_sha256": sha(original),
        "actual_literals": strings,
        "compile_results": compile_results,
        "all_seven_rfl_equalities_kernel_checked": True,
        "source_and_patch_sha256": {f: sha(ROOT / f) for f in [
            "Export.lean", "Main.lean", "lean419.patch", "string-lowering.patch",
            "StringLoweringCases.lean", "lowering_gate.py", "LICENSE"]},
        "artifact_sha256": {f: sha(ROOT / f) for f in
                            ["Export.olean", "Main.olean", "StringLoweringCases.olean"]},
        "external_checker_run": False,
        "full_packet_export_pending": True,
    }
    (ROOT / "lowering-result.json").write_text(json.dumps(record, indent=2) + "\n", "utf-8")
    print(json.dumps({"all_seven_rfl_equalities_kernel_checked": True,
                      "adapted_exporter_sha256": sha(ROOT / "Export.lean"),
                      "patch_sha256": sha(ROOT / "string-lowering.patch"),
                      "receipt_sha256": sha(ROOT / "lowering-result.json")}, indent=2))


if __name__ == "__main__":
    main()
