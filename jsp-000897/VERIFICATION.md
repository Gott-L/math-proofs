# Verification record — JSP-000897 / Erdős 1079

The integrated Lake build and separate named-axiom audit both completed successfully on 20 September 2026. Four mathematical modules and the Audit module form the default library target. The two small auxiliary component audits are also included so every source hash recorded by the runner is reproducible.

- `build`: exit 0, 1565.094 seconds; started 2026-09-20T11:16:55.223761+00:00.
- `axioms`: exit 0, 13.625 seconds; started 2026-09-20T11:43:00.328057+00:00.

Compiler: Lean 4.19.0, compiler commit `6caaee842e94`. Mathlib is pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`, with transitive package pins in `lake-manifest.json`.

The actual commands, times, exit codes and output hashes are in [result.json](verification/integrated-01/result.json). Their unedited [build stdout](verification/integrated-01/build-stdout.txt), [build stderr](verification/integrated-01/build-stderr.txt), [audit stdout](verification/integrated-01/axioms-stdout.txt) and [audit stderr](verification/integrated-01/axioms-stderr.txt) are retained. Both checking commands treat project warnings as errors. Source hashes were taken before the run and checked again afterwards.

All **16 named theorem axiom lists** contain only `propext`, `Classical.choice`, and `Quot.sound` (or a subset). No endpoint relies on `sorryAx`, a custom unproved axiom, or a native-computation axiom. The audit also prints the two full quantified statements. The four source modules contain no proof placeholders or custom axiom declarations.

## Reproduction and trust boundary

From this directory with the pinned toolchain installed, obtain the pinned packages and their standard cache with `lake exe cache get`, then run `python verify.py --label your-check`. This runs `lake build` followed by `lake env lean -DwarningAsError=true Audit.lean`. A fresh checkout has no local project build products.

Our execution used an isolated Mathlib source worktree at the pinned commit and available standard dependency caches, supplementing missing graph modules. Lake also rebuilt dependency modules whose cache records were not current. This is not a claim that every dependency or the compiler was rebuilt from source or independently kernel-replayed. Local caches were assembled from same-version standard Mathlib artifacts; no prior problem-specific theorem or proof module was imported. Absolute machine paths in the raw records describe the actual execution environment and are not required paths for a new installation.

The [semantic review](internal-review-b.md) and [source-import audit](dependency-review-c.md) were performed by agents in the same project, each with their implementation involvement disclosed. They are internal checks, not official acceptance or outside independent review. The import audit verifies the absence of Turán's theorem and exact extremal-number formula in this implementation's source dependency closure; it does not assert smaller proof terms, faster compilation, historical novelty, or eligibility for a prize.

## Frozen source hashes

| File | SHA-256 |
| --- | --- |
| `Audit.lean` | `a7ececeaac3d24edb55d2cbbe7e746de8dee072aa58259ff8db9945af1a2e953` |
| `DegreeBound.lean` | `b23910886ae63b60a2e7c8ee979bec7ac7ef80ce5754a1100859d841be6f6de6` |
| `JoinBound.lean` | `6eddc1bdf38a9237df5880ab0d7d88e95e898039bf352d3cbf034c80e4773075` |
| `Main.lean` | `10c81035619eab00f86a4a1381e945cc6b024862c8fe882ea406b759a71f8260` |
| `NeighborhoodAudit.lean` | `d51dd53d8f7c04610a900dfad86e43895e2f48068ff9e029ebd6b518289ce956` |
| `NeighborhoodBound.lean` | `061450968678033f52dd8d8b33da967a7e646e5d8fcbaf4a6a66eb0148b897ad` |
| `ProbeJoin.lean` | `193e0403abc0dbe24ec938222602c55f935a3fa26540322df34025a52e5bf03a` |
