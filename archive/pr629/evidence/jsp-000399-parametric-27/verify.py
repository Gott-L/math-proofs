"""Reproduce the Lean kernel check in a new directory, with no Mathlib dependency."""
import argparse
import hashlib
import json
import os
import pathlib
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = pathlib.Path(__file__).resolve().parent
parser = argparse.ArgumentParser()
parser.add_argument("--lean", default="lean", help="Lean 4.19.0 executable")
parser.add_argument("--receipt", type=pathlib.Path)
args = parser.parse_args()
lean = shutil.which(args.lean)
if lean is None:
    parser.error("Lean executable not found")
env = os.environ.copy()
env["ELAN_TOOLCHAIN"] = "leanprover/lean4:v4.19.0"
version = subprocess.run([lean, "--version"], text=True, capture_output=True, check=True, env=env)
if "version 4.19.0," not in version.stdout:
    parser.error("This packet is pinned to Lean 4.19.0")
modules = {
    "Jsp399TripleCore": ["JSP399TwentySeven." + name for name in ["triples_complete", "triples_nodup", "triples_length", "sortWithFuel_perm"]],
    "Jsp399Witness": ["JSP399TwentySeven." + name for name in ["A_strict", "B_strict", "A_positive", "B_positive", "different_sets"]],
    "EncodedCoeffCertificate": ["JSP399CoeffCertificate." + name for name in ["encoded_sums_A", "encoded_sums_B", "sorted_encoded_sums_equal", "encoded_triple_sums_perm"]],
    "Jsp399Parametric": ["JSP399Parametric." + name for name in ["vector_triple_sums_perm", "every_additive_image_collision", "every_parameter_collision", "every_translated_parameter_collision", "example_is_nontrivial_collision"]],
}
allowed = {"propext", "Classical.choice", "Quot.sound"}
checks = []
with tempfile.TemporaryDirectory(prefix="jsp399-check-") as temporary:
    # Replace inherited library search paths: only freshly built local modules
    # and the pinned compiler's bundled libraries may satisfy imports.
    env["LEAN_PATH"] = temporary
    for module in modules:
        shutil.copyfile(ROOT / (module + ".lean"), pathlib.Path(temporary) / (module + ".lean"))
    for module, expected in modules.items():
        source = ROOT / (module + ".lean")
        command = [lean, "-s", "65536", "-DwarningAsError=true", "-o", module + ".olean", source.name]
        result = subprocess.run(command, cwd=temporary, text=True, encoding="utf-8", capture_output=True, env=env)
        output = result.stdout + result.stderr
        audit_lines = [s for s in output.splitlines() if "depends on axioms:" in s or "does not depend on any axioms" in s]
        audit_ok = len(audit_lines) == len(expected)
        for name in expected:
            lines = [s for s in audit_lines if s.startswith("'" + name + "'")]
            if len(lines) != 1:
                audit_ok = False
                continue
            match = re.search(r"depends on axioms: \[(.*)\]", lines[0])
            if match:
                axioms = {s.strip() for s in match.group(1).split(",") if s.strip()}
                audit_ok &= axioms <= allowed
            elif "does not depend on any axioms" not in lines[0]:
                audit_ok = False
        checks.append({
            "source_file": source.name,
            "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
            "source_bytes": source.stat().st_size,
            "command": " ".join(["lean"] + command[1:]),
            "exit_code": result.returncode,
            "axiom_audit_passed": bool(audit_ok),
            "output": output,
        })
        if result.returncode != 0:
            break
passed = len(checks) == len(modules) and all(c["exit_code"] == 0 and c["axiom_audit_passed"] for c in checks)
receipt = {
    "compiler": version.stdout.strip(),
    "fresh_temporary_directory": True,
    "external_libraries": [],
    "all_checks_passed": passed,
    "checks": checks,
    "limitations": "Same Lean distribution and kernel; not an independent kernel implementation or official prize verification."
}
serialized = json.dumps(receipt, indent=2) + "\n"
if args.receipt:
    args.receipt.write_text(serialized, encoding="utf-8")
print(serialized)
sys.exit(0 if passed else 1)
