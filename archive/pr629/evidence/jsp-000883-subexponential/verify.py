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
MODULES = ['CarryCompatibility', 'OneCarry', 'FiniteConstruction', 'Simultaneous', 'PrimeCountBound', 'SizeBounds', 'SubexpParameters', 'SubexpAsymptotic', 'SubexpInfimum', 'SubexpNonempty', 'SubexpSubmission']
THEOREMS = ['Nat.choose_ne_zero', 'Nat.factorization_eq_zero_of_not_prime', 'Nat.factorization_choose', 'Nat.factorization_eq_card_pow_dvd_of_lt', 'Erdos1063.carry_of_mod_lt', 'Erdos1063.one_carry', 'Erdos1063.prime_power_dvd_choose', 'Erdos1063.high_power_carry', 'Erdos1063.truncated_covering', 'Erdos1063.low_power_count', 'Erdos1063.truncated_covering_of_min', 'Erdos1063.large_prime_automatic', 'Erdos1063.anchored_residue', 'Erdos1063.anchored_covering', 'Erdos1063.off_center_valuation', 'Erdos1063.anchor_carry_lower_bound', 'Erdos1063.small_prime_anchor', 'Erdos1063.exceptional_large_prime', 'Erdos1063.carry_iff_mod_lt', 'Erdos1063.no_late_carry', 'Erdos1063.center_fails', 'Erdos1063.depth', 'Erdos1063.radius', 'Erdos1063.offsetDepth', 'Erdos1063.lowCarries', 'Erdos1063.deficit', 'Erdos1063.small_prime_from_depth', 'Erdos1063.prime_divisor_deficit', 'Erdos1063.center_fails_at_prime_divisor', 'Erdos1063.dvd_choose_of_local', 'Erdos1063.constructionPrimes', 'Erdos1063.anchorExponent', 'Erdos1063.anchorProduct', 'Erdos1063.anchorProduct_ge', 'Erdos1063.anchor_divides_product', 'Erdos1063.failure_power_divides_product', 'Erdos1063.finite_witness', 'Erdos1063.same_box_close', 'Erdos1063.simultaneous_boxes', 'Erdos1063.close_residue_carry', 'Erdos1063.difference_carry', 'Erdos1063.exists_regular_multiplier', 'Erdos1063.regularPrimes', 'Erdos1063.exists_bounded_witness', 'Erdos1063.primeCount', 'Erdos1063.primeCount_mul_log_le', 'Erdos1063.small_remainder_count', 'Erdos1063.active_prime_count', 'Erdos1063.anchor_factor_le', 'Erdos1063.anchorProduct_le', 'Erdos1063.regular_card_le', 'Erdos1063.exists_coarse_bounded_witness', 'Erdos1063.scale', 'Erdos1063.center', 'Erdos1063.cost', 'Erdos1063.exponentCost', 'Erdos1063.scale_pow_le', 'Erdos1063.scale_ge_of_pow_le', 'Erdos1063.lt_scale_succ_pow', 'Erdos1063.parameter_arithmetic', 'Erdos1063.scale_ge_two', 'Erdos1063.scale_fourth_pow_le', 'Erdos1063.exponentCost_mul_scale', 'Erdos1063.parameter_witness', 'Erdos1063.anchor_log_bound', 'Erdos1063.eventually_anchor_log_bound', 'Erdos1063.prime_log_bound_of_count', 'Erdos1063.prime_log_bound', 'Erdos1063.coarseBound', 'Erdos1063.eventually_coarse_bound', 'Erdos1063.exists_degree_small_rate', 'Erdos1063.exists_subexponential_coarse_bound', 'Erdos1063.subexponential_witness', 'Erdos1063.Admissible', 'Erdos1063.leastWitness', 'Erdos1063.leastWitness_le', 'Erdos1063.leastWitness_spec_of_exists', 'Erdos1063.eventually_leastWitness_exp_of_witnesses', 'Erdos1063.log_leastWitness_isLittleO_of_witnesses', 'Erdos1063.admissible_exists', 'Erdos1063.leastWitness_spec', 'Erdos1063.leastWitness_ge', 'Erdos1063.admissible_subexponential_witness', 'Erdos1063.leastWitness_subexponential', 'Erdos1063.erdos_1063.subexponential_upper', 'Erdos1063.log_leastWitness_div_tendsto_zero']
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB_REV = "c44e0c8ee63ca166450922a373c7409c5d26b00b"


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
    installed = run(["git", "rev-parse", "HEAD"], cwd=ROOT / ".lake/packages/mathlib").strip()
    if installed != MATHLIB_REV:
        raise RuntimeError("The installed Mathlib checkout differs from the pinned revision.")

    receipt = {"verified_at_utc": datetime.now(timezone.utc).isoformat(),
               "lean_version": version, "mathlib_commit": MATHLIB_REV,
               "method": "fresh local source compilation using pinned dependency cache",
               "standard_axiom_allowlist": sorted(ALLOWED_AXIOMS),
               "modules": [], "axiom_audit": {}}
    with tempfile.TemporaryDirectory(prefix="erdos1063-subexp-proof-") as temporary:
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
            if re.search(r"\b(sorry|admit|native_decide|unsafe|axiom)\b", content):
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
        receipt["typed_endpoint_checks"] = ['literal_admissibility', 'literal_natural_infimum', 'all_k_nonemptiness', 'actual_minimum_admissible', 'epsilon_witness_with_unique_exception', 'literal_infimum_exponential_bound', 'log_minimum_little_o', 'log_minimum_ratio_limit', 'actual_prime_count_bound', 'full_finite_witness_bound']
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
