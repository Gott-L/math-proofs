# Executed verification

PASS: the complete five-root Lake library build and a separate named-axiom audit both exited successfully on 2026-09-20. This records local Lean verification, not organizer acceptance or an independent external review.

## Toolchain and executed commands

Lean **4.19.0**, Lake **5.0.0-6caaee8**, Mathlib **c44e0c8ee63ca166450922a373c7409c5d26b00b**. The manifest pins all nine dependency repositories; their checked-out revisions matched and their tracked sources were clean before this run.

The runner was invoked from Windows using:

```text
D:/miniconda3/python.exe -X utf8 verify.py --lake D:/codex/p_vs_np_investigation/toolchain/lean-4.19.0-windows/bin/lake.exe --label integrated-b-01
```

It cleared inherited `LEAN_PATH` and `LEAN_SRC_PATH`, then executed these commands in the project directory:

```sh
lake build
lake env lean -DwarningAsError=true Audit.lean
```

| Command | Started (UTC) | Exit | Elapsed |
|---|---|---:|---:|
| build | 2026-09-20T12:16:12.401964+00:00 | 0 | 308.484 s |
| axioms | 2026-09-20T12:21:20.888895+00:00 | 0 | 11.062 s |

The integrated build rebuilt `PositiveIdempotent`, `TrianglePatterns`, `FiniteBridge`, `Main` and `Audit`. Project warnings were errors. The separate audit reported all **19** declarations listed by `Audit.lean`, with only `propext`, `Classical.choice`, and `Quot.sound` or a subset. In particular, `GottL746.erdos_895` has only these standard three axiom dependencies; its finite-graph conclusion has no unproved infinite-graph hypothesis.

## Cache reuse and trust boundary

For this local run, dependency source trees were separate detached worktrees at the manifest pins. Existing Lake artifacts and trace files from the earlier JSP897 build were **copied**, not linked, into these new worktrees. Lake rebuilt missing or stale standard dependencies, including the topology/Hindman chain. The build did not use the temporary per-module `dependencies/olean` overlay or a problem-specific module from another project.

This is not a clean rebuild of all dependencies, an independent kernel recheck of all cached Mathlib declarations, or verification of the Lean executable itself. It trusts Lean and the reused pinned dependency artifacts. Cache preparation and compilation wrote only the new project directory apart from Git worktree registration metadata; no old proof sources or old cached build artifacts were replaced.

The portable configuration requires the public pinned Mathlib Git repository and contains no local dependency paths. On a normal checkout, use `lake exe cache get` followed by `python verify.py --label my-check`. A new label preserves earlier run evidence. The local-only `prepare_cached_packages.py` script is not needed for public reproduction.

## Fixed sources and configuration

All files below were hashed before both checks and remained byte-identical at completion.

| File | Bytes | SHA256 |
|---|---:|---|
| [Audit.lean](Audit.lean) | 915 | `5be4cfbf3f54a1e4dc0cfc5fba2d80c31e2e4c5f744d77c6dd8d7955377af80f` |
| [FiniteBridge.lean](FiniteBridge.lean) | 5759 | `e375533ae4d20a936ab454d0b939ebb16d3e03ae95f38f95345e26fec71189c8` |
| [Main.lean](Main.lean) | 3049 | `9cb9ec2d74ed017ac2a247c23c8141f97fb6186e284de8641aca787119102e19` |
| [PositiveIdempotent.lean](PositiveIdempotent.lean) | 2073 | `50ba0677486033726c85197720a11bf02b1878a7487ee191e2fbff304e7b1d64` |
| [TrianglePatterns.lean](TrianglePatterns.lean) | 4250 | `8e2cf6f394ca8312b96b82b00970f73e555ee16d2e51f7095fc6771599bdeba7` |
| [lakefile.toml](lakefile.toml) | 437 | `03d04a80c45ba3992bef2271c8a058888e3a049f8c004a7f00e23c40a2199847` |
| [lake-manifest.json](lake-manifest.json) | 3640 | `4a52edbaa50563f5c202b4869926a6a162195a0b53e8ee8428ee63e67b801b00` |
| [lean-toolchain](lean-toolchain) | 25 | `55e97be96000b5e9e290c9e74482e5e317861499a5540353ce845471bded8cea` |

## Actual output records

[Structured result](verification/integrated-b-01/result.json) records the exact commands, absolute local working directory, dependency revisions, source identities, durations and all 19 axiom lists. Both stderr files are empty.

| Record | Bytes | SHA256 |
|---|---:|---|
| [verification/integrated-b-01/result.json](verification/integrated-b-01/result.json) | 7450 | `7b6d8512919b2cf3f6f0b7c29b545dfba92bf24e4fb4f68c1e81cde6bef66e71` |
| [verification/integrated-b-01/build-stdout.txt](verification/integrated-b-01/build-stdout.txt) | 7849 | `f3b7b5a36692eb3b3e8ba66cbabbca017e7f86c34a9b066605277c9d1c51fc7f` |
| [verification/integrated-b-01/build-stderr.txt](verification/integrated-b-01/build-stderr.txt) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| [verification/integrated-b-01/axioms-stdout.txt](verification/integrated-b-01/axioms-stdout.txt) | 1777 | `05806f28e7db075a346e3106f193be78dd532270964bcf987cae117322a37e68` |
| [verification/integrated-b-01/axioms-stderr.txt](verification/integrated-b-01/axioms-stderr.txt) | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| [verify.py](verify.py) | 5076 | `b29ed1d968cd84a7da2f4b11ab9d4b61601306b13aed7aab4790bb94a46faef7` |

The build was run by the Codex agent that authored `FiniteBridge.lean`; mathematical cross-review is documented separately. This is same-team validation. It does not establish mathematical novelty, priority, prize eligibility, or official verification status.
