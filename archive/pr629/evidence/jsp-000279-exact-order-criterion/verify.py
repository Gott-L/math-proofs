#!/usr/bin/env python3
"""Compile every local proof in a fresh directory and audit its axiom dependencies."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
MODULES = ['E336Defs', 'E336Differences', 'E336Padding', 'E336Necessity', 'E336Criterion']
THEOREMS = ['E336.RepresentsExactly', 'E336.EventuallyExactly', 'E336.EventuallyAtMost', 'E336.HasExactOrder', 'E336.DifferenceGcdOne', 'E336.ConsecutiveGcdOne', 'E336.AdjacentLengths', 'E336.BalancedDifference', 'E336.balancedDifference_zero', 'E336.balancedDifference_add', 'E336.balancedDifference_neg', 'E336.balancedDifference_sub', 'E336.balancedDifference_nat_mul', 'E336.balancedDifference_dist', 'E336.balancedDifference_mod', 'E336.differenceGcdOne_nonempty', 'E336.exists_positive_balancedDifference', 'E336.balancedDifference_one', 'E336.adjacentLengths_of_differenceGcdOne', 'E336.representsExactly_zero', 'E336.representsExactly_add', 'E336.representsExactly_adjacent_padding', 'E336.eventuallyExactly_of_adjacent_representations', 'E336.eventuallyExactly_of_adjacentLengths', 'E336.modEq_iff_dvd_dist', 'E336.list_sums_modEq', 'E336.differenceGcdOne_of_eventuallyExactly', 'E336.pairwise_dvd_iff_consecutive_dvd', 'E336.differenceGcdOne_range_iff', 'E336.exists_eventuallyExactly_iff', 'E336.exists_hasExactOrder_iff_exists_eventuallyExactly', 'E336.erdos_graham_set_criterion', 'E336.erdos_graham_sequence_criterion', 'E336.eventuallyExactly_pos']
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB_REV = "c44e0c8ee63ca166450922a373c7409c5d26b00b"


def strip_lean_comments(source):
    """Remove nested block and line comments for the additional lexical check."""
    result = []
    depth = 0
    in_string = False
    index = 0
    while index < len(source):
        pair = source[index:index + 2]
        ch = source[index]
        if depth:
            if pair == "/-":
                depth += 1
                index += 2
            elif pair == "-/":
                depth -= 1
                index += 2
                result.append(" ")
            else:
                if ch == "\n":
                    result.append(ch)
                index += 1
        elif in_string:
            if ch == "\\":
                index += 2
            else:
                if ch == '"':
                    in_string = False
                index += 1
        elif ch == '"':
            in_string = True
            result.append(" ")
            index += 1
        elif pair == "/-":
            depth = 1
            index += 2
        elif pair == "--":
            newline = source.find("\n", index)
            index = len(source) if newline < 0 else newline
        else:
            result.append(ch)
            index += 1
    if depth or in_string:
        raise RuntimeError("Unterminated source comment or string")
    return "".join(result)


def run(command, *, cwd=ROOT, env=None, timeout=600):
    proc = subprocess.run(command, cwd=cwd, env=env, capture_output=True,
                          text=True, encoding="utf-8", errors="replace", timeout=timeout)
    if proc.returncode:
        raise RuntimeError(f"Command failed ({proc.returncode}): {command}\n"
                           f"{proc.stdout}\n{proc.stderr}")
    return proc.stdout + proc.stderr


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inside-lake", action="store_true", help=argparse.SUPPRESS)
    args = parser.parse_args()
    if not args.inside_lake:
        lake = shutil.which("lake")
        if not lake:
            raise RuntimeError("Install the pinned Lean toolchain and put lake on PATH.")
        result = subprocess.run([lake, "env", sys.executable, str(Path(__file__).resolve()),
                                 "--inside-lake"], cwd=ROOT)
        return result.returncode

    lean = shutil.which("lean")
    if not lean:
        raise RuntimeError("The Lake environment did not expose Lean.")
    version = run([lean, "--version"]).strip()
    if "version 4.19.0" not in version:
        raise RuntimeError(f"Unexpected Lean version: {version}")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    if mathlib["rev"] != MATHLIB_REV:
        raise RuntimeError("The manifest does not pin the expected Mathlib revision.")
    dependency_versions = {}
    for package in manifest["packages"]:
        installed = run(["git", "rev-parse", "HEAD"], cwd=ROOT / ".lake/packages" / package["name"]).strip()
        if installed != package["rev"]:
            raise RuntimeError("Installed dependency differs from its pinned revision: " + package["name"])
        dependency_versions[package["name"]] = installed

    receipt = {"verified_at_utc": datetime.now(timezone.utc).isoformat(),
               "lean_version": version, "mathlib_commit": MATHLIB_REV,
               "method": "fresh local source compilation using pinned dependency cache",
               "standard_axiom_allowlist": sorted(ALLOWED_AXIOMS),
               "modules": [], "axiom_audit": {}, "dependency_versions": dependency_versions}
    with tempfile.TemporaryDirectory(prefix="e336-exact-order-proof-") as temporary:
        target = Path(temporary)
        env = os.environ.copy()
        # Lake can expose relative search paths. Resolve them before changing
        # working directory, and exclude old project-local build products.
        old_build = (ROOT / ".lake/build/lib/lean").resolve()
        dependency_paths = []
        for entry in env.get("LEAN_PATH", "").split(os.pathsep):
            if not entry:
                continue
            resolved = (ROOT / entry).resolve()
            if resolved != old_build:
                dependency_paths.append(str(resolved))
        env["LEAN_PATH"] = os.pathsep.join([str(target)] + dependency_paths)
        for module in MODULES:
            source = ROOT / f"{module}.lean"
            data = source.read_bytes()
            content = data.decode("utf-8")
            if re.search(r"\b(sorry|admit|native_decide|unsafe|axiom)\b", strip_lean_comments(content)):
                raise RuntimeError(f"Disallowed proof-source token in {source.name}")
            (target / source.name).write_bytes(data)
        for module in MODULES:
            before = time.monotonic()
            output = run([lean, "-s", "65536", "-DwarningAsError=true", "-o",
                          f"{module}.olean", f"{module}.lean"], cwd=target, env=env)
            data = (target / f"{module}.lean").read_bytes()
            receipt["modules"].append({"file": f"{module}.lean", "bytes": len(data),
                "sha256": hashlib.sha256(data).hexdigest(), "passed": True,
                "seconds": round(time.monotonic() - before, 3)})
            print(f"PASS {module}.lean", flush=True)
            if output.strip():
                print(output.strip(), flush=True)
        audit_source = ROOT / "TypedAudit.lean"
        audit_data = audit_source.read_bytes()
        audit = audit_data.decode("utf-8") + "\n" + "\n".join(
            f"#print axioms {name}" for name in THEOREMS) + "\n"
        receipt["typed_audit_source_sha256"] = hashlib.sha256(audit_data).hexdigest()
        (target / "Audit.lean").write_text(audit, encoding="utf-8")
        output = run([lean, "-s", "65536", "-DwarningAsError=true", "Audit.lean"],
                     cwd=target, env=env)
        for name in THEOREMS:
            full = name
            match = re.search(re.escape("'" + full + "'") +
                              r" depends on axioms:\s*\[([^]]*)\]", output)
            if match:
                dependencies = [s.strip() for s in match.group(1).split(",") if s.strip()]
            elif "'" + full + "' does not depend on any axioms" in output:
                dependencies = []
            else:
                raise RuntimeError(f"Missing named axiom audit: {full}\n{output}")
            if not set(dependencies) <= ALLOWED_AXIOMS:
                raise RuntimeError(f"Unapproved dependency for {full}: {dependencies}")
            receipt["axiom_audit"][full] = dependencies
        receipt["passed"] = True
        receipt["typed_endpoint_checks"] = ['raw_set_iff', 'raw_least_order_iff', 'raw_sequence_consecutive_iff', 'unconditional_finite_adjacent_certificate', 'explicit_padding_bound', 'repeated_summands', 'empty_representation', 'zero_not_eventual_order']
    (ROOT / "verification.json").write_text(json.dumps(receipt, ensure_ascii=False, indent=2)
                                            + "\n", encoding="utf-8")
    print(f"PASS all {len(MODULES)} modules and {len(THEOREMS)} named axiom audits.")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except Exception as exc:
        print(f"Verification failed: {exc}", file=sys.stderr)
        sys.exit(1)
