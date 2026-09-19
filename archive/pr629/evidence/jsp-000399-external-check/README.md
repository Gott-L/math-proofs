# External kernel-checker supplement for JSP-000399

Under Gott-L's project initiation, direction, and submission management, the Codex-assisted team independently checked the **ten named endpoints and semantic bridges of the five-parameter 27-point packet** with Nanoda, a separately implemented Lean kernel checker. The positive run accepted **2,882 declarations** on 17 September 2026. Two deliberately invalid versions of the central vector-identity theorem were rejected for the expected reasons.

This supplement concerns **one existing proof packet**. The other proof packets in the combined submission were not checked by this run. The checker was operated by the same team; this is not independent human review, official prize verification, a new mathematical result, a first-formalization claim, or a funding decision. The mathematical scope and prior attribution remain those of the [original packet at the checked commit](https://github.com/Gott-L/awards/tree/86cf6d9a47a7134e9901c6464322eafddc89742e/evidence/jsp-000399-parametric-27).

## Exactly what passed

The proof sources are the unchanged four files from `Gott-L/awards@86cf6d9a47a7134e9901c6464322eafddc89742e`, originally submitted in [PR 629](https://github.com/TheJustinSunPrize/awards/pull/629). Their fresh compilation used Lean **4.19.0**, `--trust=0`, and the standard library, without Mathlib. `records/proof-fresh.redacted.json` records the successful fresh builds; the earlier resource-related compiler failure and the subsequent serial-elaboration retry are retained there rather than hidden.

| File | SHA-256 |
| --- | --- |
| `Jsp399TripleCore.lean` | `ec6d0d0bf114c025bbcd5a82a77d3b0401433a2df630438a3f60e602f76b7ee4` |
| `Jsp399Witness.lean` | `4f1937d3fe11b213adb5fe3301e0bb0fd546238063993521fd26ca32da525503` |
| `EncodedCoeffCertificate.lean` | `2d64c4d56c8963a45597d8f933fb71e08b0d8e3f08f7a6ff057c588faaa94f23` |
| `Jsp399Parametric.lean` | `fd486be111060dafac013d577fc75152b4ff1139187f5def7332efd15d832e77` |

The explicit roots were:

| Namespace | Roots | Mathematical role |
| --- | --- | --- |
| `JSP399TwentySeven` | `triples_complete`, `triples_nodup`, `triples_length` | The list represents each increasing triple of 27 indices exactly once and has 2,925 entries. |
| `JSP399Parametric` | `vector_triple_sums_perm` | Equality, including multiplicities, of the two coefficient-vector spectra. |
| `JSP399Parametric` | `every_additive_image_collision`, `every_parameter_collision`, `every_translated_parameter_collision` | Additive transport, every five-integer parameter choice, and a common translation. |
| `JSP399Parametric` | `example_is_nontrivial_collision` | Two positive, distinct-entry 27-element examples with different underlying sets and equal spectra. |
| `JSP399Parametric` | `exampleA_matches`, `exampleB_matches_reverse` | The concrete theorem agrees with the displayed integer lists, with the documented reverse ordering for the second list. |

The arbitrary parameter results allow repeated evaluated values. Distinct positive sets are established by the concrete example theorem, not presumed for every parameter. The enumeration lemmas were explicit roots because they need not occur automatically in a collision theorem's proof dependencies. See `reviews/target-audit.md` and `logs/full-lowered.valid.declarations.txt` for the actual statements and scope explanation.

## Checker and recorded outcome

The unchanged checker source is [ammkrn/nanoda_lib@4c544ed4099c8227f07d5de77ad1e69fb0740a27](https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27), built with **Rust 1.93.0**, `cargo build --release --locked --bin nanoda_bin -j 1`. Its source manifest and successful build receipt are included. The recorded Linux binary SHA-256 is `bd60ccdb0f08f6a1115975c135ec4117dee3a4ff4daab9278f8e9e0d75871d2e`; binaries are not included.

The input was 10,385,356 bytes, SHA-256 `43ccad2ef5605b915c0decce923d46245e6da876aed2058ddc603b0ec285a839`. It contains all ten genuine theorem records, 2,882 declarations, and zero string-literal records. The checker reported `Checked 2882 declarations with no errors`, exit 0, and printed all ten requested declarations. The positive run took approximately 31 seconds on the recorded host; that is not a performance guarantee for other machines.

The policy permitted only `propext`, `Classical.choice`, and `Quot.sound`, with hard errors for unpermitted axioms and unknown requested declarations. `unsafe_permit_all_axioms` was false; one checking thread and the natural-number extension were enabled; the string extension was disabled. The runner separately rejected missing theorem records, pretty-printer errors, timeouts, and mismatched source/export provenance rather than relying only on an exit code or success banner.

Both negative controls targeted **`JSP399Parametric.vector_triple_sums_perm`**, retaining its name, type, and universe parameters:

- Replacing only its proof-value reference with an already exported natural-number expression produced the expected type-equality assertion failure, exit 101.
- Replacing that theorem with an unpermitted axiom produced the expected named unpermitted-axiom error, exit 1.

Exactly one declaration record changed in each control. These are two controls on that central theorem, **not twenty controls separately repeated for all ten roots**. `records/checker-result.redacted.json` contains the structured differences, full success flags, input hashes, and log hashes. The original positive input was preserved throughout. No network isolation or independent operator is claimed.

## Disclosed exporter adaptations

The base exporter is [leanprover/lean4export@076e8e57707e813375e8f9da8bf989799ace9680](https://github.com/leanprover/lean4export/tree/076e8e57707e813375e8f9da8bf989799ace9680), whose own toolchain selects Lean 4.34. The archived source was first backported to the existing Lean 4.19 APIs, then adapted to lower seven actual string literals into the ordinary Lean 4.19 `String.mk (List Char)` representation. Nanoda and the submitted proof sources were not changed.

Both separate patches are included, alongside the final `exporter/Export.lean`, unchanged `exporter/Main.lean`, upstream source hashes, and Apache-2.0 notices. The first patch adjusts `NameMap` operations, JSON method notation, and the `Expr.letE` constructor while preserving its `nonDep := false` normalization. The second recursively expands strings using exact `Char.ofNat` codepoints before expression interning and explicitly exports all introduced dependencies. Residual string literals cause an error. The actual export used the default metadata-removing path; metadata-preserving export is outside this pilot's supported scope.

Each of the seven literal-to-constructor equalities was separately proved by Lean 4.19 kernel `rfl`, with no axioms. A second internal collaborator independently regenerated those checks and compared all 2,882 original and lowered declarations: types, values, universes, and recursor right-hand sides matched modulo exactly the reviewed string expansions, with no missing or additional declarations. The comparison correctly models Lean 4.19's `mkNatLit` as an `OfNat` expression rather than a raw literal. The source, logs, and corrected comparison receipt are included under `reviews/` and `literal-checks/`. This is an additional same-team audit, not external human endorsement.

The exporter metadata identifies the adaptation as `lean4export-lean4.19-string-lowered`, version `3.1.0+lean4.19.string-lowered`, and truthfully reports Lean 4.19.0 / commit `6caaee842e9495688c1567e78c0e68dbb96942aa`, format 3.1.0. It does not claim to be the unmodified upstream exporter.

## Reproduction

Prerequisites are Python 3.10+, an existing Lean 4.19.0 distribution, an existing Rust 1.93.0/Cargo toolchain with a working linker, and the pinned Nanoda source checkout. The proof sources can be obtained from the linked checked commit; in the evidence repository they are the sibling `../jsp-000399-parametric-27/` directory. Their hashes are enforced by the replay helper.

The **recorded run** used Windows Lean and a Linux Nanoda binary in an existing WSL Ubuntu distribution. The exact runner and export-driver sources used for that run are archived in `scripts/`, with original hashes in the receipts. Their original working-directory layout and machine paths are described by the path-redacted records, not silently presented as generic commands.

`scripts/replay.py` is a new convenience driver for **native same-host** Lean/Cargo/checker execution. It accepts explicit `--lean`, `--cargo`, `--nanoda-src`, `--proof-dir`, and `--work-dir` paths; checks pinned inputs; freshly compiles the four proof modules and adapted exporter; builds Nanoda; exports the ten roots; and runs the same positive/negative checks. It requires a fresh empty work directory. It does not install toolchains or fetch a Mathlib cache. Cargo may fetch its locked Rust dependencies. This new driver was syntax/help checked during preparation but **has not been run end-to-end**; the actual success evidence is the recorded operator run, not this prospective wrapper.

```text
python scripts/replay.py --lean /path/to/lean --cargo /path/to/cargo --nanoda-src /path/to/pinned/nanoda_lib --proof-dir ../jsp-000399-parametric-27 --work-dir /path/to/fresh-replay
```

On Windows, native tool executables must match the host. To repeat the recorded mixed Windows/WSL arrangement instead, use the archived `run_nanoda.recorded.py` runner with an explicit Linux binary/build receipt and a prepared input; do not supply a Linux Cargo executable directly to Windows Python. The main build/export commands and exact ten-root list are also recorded in the receipts. The `lean --run` exporter invocation requires **two** separators before the roots because the Lean CLI consumes one:

```text
lean --trust=0 -s 65536 -j 1 -DElab.async=false --run Main.lean Jsp399Parametric -- -- JSP399TwentySeven.triples_complete JSP399TwentySeven.triples_nodup JSP399TwentySeven.triples_length JSP399Parametric.vector_triple_sums_perm JSP399Parametric.every_additive_image_collision JSP399Parametric.every_parameter_collision JSP399Parametric.every_translated_parameter_collision JSP399Parametric.example_is_nontrivial_collision JSP399Parametric.exampleA_matches JSP399Parametric.exampleB_matches_reverse
```

Only the fresh proof and exporter directories plus the pinned bundled libraries should satisfy imports. The original pilot enforced a cumulative storage limit and a 100 MiB export/control-copy cap. Replays need their own appropriate resources; no large dependency cache or another Lean version is required by this Std-only packet.

## Publication contents, privacy, and provenance

This directory contains only the explicit files listed in `MANIFEST.json`. Large NDJSON inputs and negative-control copies, binaries, `.olean` files, Rust runtime/dependencies, and local caches are omitted; the scripts regenerate them. The input and binary hashes remain in the records. `verify_supplement.py` checks the published whitelist and hashes without executing proofs or downloading anything.

Files labelled `.redacted.json` are copies of actual receipts/configurations with machine-local path strings replaced by `<pilot>`, `<lean-toolchain>`, or similar portable placeholders. Their mathematical targets, policies, outcomes, timestamps, input/log/source hashes, and control differences are unchanged. Hash fields referring to an original receipt or configuration continue to identify the **original unredacted bytes**. `PUBLIC-PROVENANCE.json` records both original and published hashes and explicitly lists path-only redactions. These configurations are records/templates; substitute actual local input/output paths before execution. Unmodified logs and scripts retain their original bytes. No email address, wallet, credential, or private account data is included.

Attribution is unchanged: Gott-L led and directed the project and submission; Codex assistance implemented and reviewed the formalizations and this verification work. The mathematical antecedents credited by the original packet remain credited there. The exporter and Nanoda are upstream Apache-2.0 projects; original proof licensing remains with the original packet. New supplement code is Apache-2.0. See `NOTICE` and `licenses/`.
