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
MODULES = ["E357DensityDefs", "E357Intervals", "E357DyadicBounds",
           "E357Counting", "E357DensityBridge", "E357"]
THEOREMS = [
    "Set.partialDensity", "Set.lowerDensity", "Set.partialDensity_nonneg",
    "Set.lowerDensity_nonneg", "Set.ncard_Iio_nat", "Set.partialDensity_nat_univ",
    "Set.lowerDensity_nat_eq_liminf", "Erdos357.HasDistinctSums", "Erdos357.blockSum",
    "Erdos357.blockSum_injective", "Erdos357.blockSum_le_of_linear_bound",
    "Erdos357.dyadicBlock", "Erdos357.dyadicBlock_card", "Erdos357.dyadicBlock_length_pos",
    "Erdos357.dyadicBlock_sum_lt", "Erdos357.dyadicBlock_disjoint",
    "Erdos357.no_linear_bound", "Erdos357.count_range_Iio_apply",
    "Erdos357.exists_linear_bound_of_lowerDensity_pos",
    "Erdos357.erdos_357.variants.infinite_set_lower_density",
]
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
    with tempfile.TemporaryDirectory(prefix="erdos357-proof-") as temporary:
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
        audit = """import E357
example {ι α : Type*} [Preorder ι] [AddCommMonoid α] (A : ι → α) :
    Erdos357.HasDistinctSums A ↔
      {J : Finset ι | (J : Set ι).OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, A x) := Iff.rfl
example (S T : Set ℕ) (b : ℕ) : S.partialDensity T b =
    (((S ∩ T) ∩ Set.Iio b).ncard : ℝ) / (T ∩ Set.Iio b).ncard := rfl
example (S T : Set ℕ) : S.lowerDensity T =
    Filter.atTop.liminf (fun b : ℕ =>
      (((S ∩ T) ∩ Set.Iio b).ncard : ℝ) / (T ∩ Set.Iio b).ncard) := rfl
example (A : ℕ → ℕ) (hm : StrictMono A) (hd : Erdos357.HasDistinctSums A) :
    (Set.range A).lowerDensity = 0 :=
  Erdos357.erdos_357.variants.infinite_set_lower_density A hm hd
example (A : ℕ → ℕ) (hm : StrictMono A)
    (hd : {J : Finset ℕ | (J : Set ℕ).OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, A x)) :
    Filter.atTop.liminf (fun b : ℕ =>
      (((Set.range A) ∩ Set.Iio b).ncard : ℝ) / (b : ℝ)) = 0 := by
  simpa only [Set.lowerDensity_nat_eq_liminf] using
    Erdos357.erdos_357.variants.infinite_set_lower_density A hm hd
""" + "\n".join(f"#print axioms {name}" for name in THEOREMS) + "\n"
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
        receipt["typed_endpoint_checks"] = ["generic_distinct_sums_definition",
            "partial_density_raw_formula", "lower_density_raw_formula",
            "exact_upstream_endpoint", "fully_expanded_raw_liminf_endpoint"]
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
