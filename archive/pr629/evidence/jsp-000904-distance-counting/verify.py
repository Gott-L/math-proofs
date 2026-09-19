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
MODULES = ["E1087Core", "E1087Incidence", "E1087Meaning", "E1087Quadruples",
           "E1087ColorBound", "E1087Plane", "E1087"]
THEOREMS = [
    "Erdos1087.edges", "Erdos1087.equalPairs", "Erdos1087.support",
    "Erdos1087.trianglePairs", "Erdos1087.disjointPairs", "Erdos1087.weight",
    "Erdos1087.totalWeight", "Erdos1087.badFourSets", "Erdos1087.badCount",
    "Erdos1087.support_card", "Erdos1087.equalPairs_card_partition",
    "Erdos1087.equalPairs_restrict", "Erdos1087.card_four_supersets_three",
    "Erdos1087.card_four_supersets_four", "Erdos1087.totalWeight_as_support_sum",
    "Erdos1087.totalWeight_identity", "Erdos1087.badCount_le_totalWeight",
    "Erdos1087.totalWeight_le_mul_badCount", "Erdos1087.weight_pos_iff",
    "Erdos1087.weight_pos_iff_card_image_lt", "Erdos1087.four_set_degenerate_iff",
    "Erdos1087.triangle_pair_unique_apex", "Erdos1087.orderedQuadruples",
    "Erdos1087.edgeOrientations_card", "Erdos1087.sameColorPairs_card",
    "Erdos1087.orderedQuadruples_card", "Erdos1087.monochromatic_pairs_le_ten",
    "Erdos1087.sqDist", "Erdos1087.planeColor", "Erdos1087.sqDist_pos",
    "Erdos1087.planeColor_pair", "Erdos1087.no_four_equidistant",
    "Erdos1087.four_set_has_different_edge_colors", "Erdos1087.weight_plane_le_ten",
    "Erdos1087.planeDistance", "Erdos1087.planeDistance_pos_iff",
    "Erdos1087.planeDistance_eq_iff", "Erdos1087.planeQuadruples",
    "Erdos1087.planeQuadruples_eq", "Erdos1087.two_mul_edges_card",
    "Erdos1087.planar_quadruples_identity", "Erdos1087.planar_weighted_identity",
    "Erdos1087.planar_comparison",
    "Erdos1087.planeEdgeLength", "Erdos1087.planeEdgeLength_pair",
    "Erdos1087.edge_length_color_card", "Erdos1087.planar_degenerate_iff",
    "Erdos1087.sharpSet_card", "Erdos1087.shortEdges_card",
    "Erdos1087.shortEdges_subset", "Erdos1087.shortEdges_color",
    "Erdos1087.sharpSet_weight", "Erdos1087.sharpSet_badCount",
    "Erdos1087.planar_sharpness",
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
    with tempfile.TemporaryDirectory(prefix="erdos1087-proof-") as temporary:
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
        receipt["typed_endpoint_checks"] = ["actual_edge_and_pair_objects",
            "actual_ordered_positive_distance_quadruples", "all_finite_support_identity",
            "planar_weighted_identity", "planar_comparison", "degenerate_four_set_meaning",
            "sharp_four_point_example"]
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
