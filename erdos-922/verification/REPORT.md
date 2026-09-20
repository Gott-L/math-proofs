# E922 verification record

The complete E922 formalization passed the local checks described below on **2026-09-19 UTC**, at historical proof commit **`b1edf8873a1a01edebbf2a12c56276223e1cbb4b`**. This is a record of those actual runs, prepared for publication on 2026-09-20. **No new build or checker run was performed while preparing this report.**

The publication package changes documentation and includes selected historical audit evidence. A separate byte-for-byte comparison on 2026-09-20 confirmed that all 29 proof modules, the original audit module, `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`, and `source-lock.json` match the historical verified version exactly. The 34 checked identities are in [SOURCE-IDENTITY.json](SOURCE-IDENTITY.json). This transfers the recorded result for the unchanged mathematical inputs; it does not assert that the publication commit received a new build or checker run.

## Statement covered

For an arbitrary simple graph `G` and one fixed natural number `k`, assume every finite vertex set `S` contains an independent subset `I` with `|S| <= 2*|I| + k`. The final theorem supplies a proper coloring `V -> Fin (k+2)`. It imposes no finiteness, countability, local-finiteness or nonemptiness assumption on `V`. The finite-subgraph formulation also allows deletion of edges. Empty sets, parity boundaries and `k=0` are included.

The [final integration module](../src/E922InfiniteEndpoint.lean) supplies the actually proved finite Folkman theorem to a compactness argument; the finite theorem is not an extra premise of the final endpoint. This formalizes a known mathematical result, not a newly solved open mathematical problem. Historical mathematics and inherited formalization credits remain as stated in the package's provenance documentation.

## Actual completed checks

| Stage | Recorded result |
| --- | --- |
| Original Lake build | `lake --no-cache -v build` exited 0. All 29 proof modules and the original audit module were freshly built. All 40 originally tracked files remained byte-identical. Build time: 1,039.656 seconds. |
| Target checks | The locally executed, fixed `lean-verify` audit script checked 11 targets using 35 successful commands: two version commands and three checks per target. Types, proof bodies and axiom dependencies were checked. These are not 35 clean builds. |
| Statement correspondence | A separately written statement harness and its equivalence bridge were compiled and checked. Same-team semantic review matched all seven original-statement requirements to the actual output, including the finite supplier and arbitrary-graph conclusion. This is an independent formulation, not a second independent proof or outside peer review. |
| Export and representation checks | Eleven roots and their dependency closure were exported. All 31 actual string values passed Lean `rfl` constructor-equivalence checks without axioms. The original and constructor-lowered exports matched on the complete set of 10,884 declarations and their full serialized fields after the explicitly permitted representation normalizations. |
| External checker | Nanoda exited 0 and reported `Checked 10884 declarations with no errors`; stderr was empty. Each of the eleven target declarations was printed exactly once. |
| Negative controls | A single deliberately invalid proof replacement was rejected with exit 101 by a type-checking assertion. A single unpermitted-axiom replacement was rejected with exit 1 and named that axiom. Neither rejection was a timeout or parser failure. |

All eleven target axiom lists were exactly **`[propext, Classical.choice, Quot.sound]`**, without `sorryAx` or additional mathematical axioms. The separate statement harness was outside the original 40-file commit and was bound independently. Its original 2,778-byte source is included unchanged as [IndependentChallenge.lean](IndependentChallenge.lean), SHA256 `919ab420f691cb2dae7d1e988fb8d86fb3bf5048e3ce880fbf65a96317bf8dd4`. It is an additional verification file, not a new default Lake target or an alteration of the original proof-source lock. After building the package, its imports can be resolved with the following command from the package root (shown for reproduction; not rerun during publication preparation):

```text
lake env lean -t0 -DwarningAsError=true verification/IndependentChallenge.lean
```

The representation comparison allowed only recorded string-constructor expansion, expression metadata erasure, the nondependent-let optimization flag, and exporter-identity metadata differences. It did not permit missing declarations, additional unchecked declarations or changed proof content.

## Environment and limits

The historical runs used WSL2 Ubuntu 24.04, native Linux Lean 4.19.0 (revision `6caaee842e9495688c1567e78c0e68dbb96942aa`) and Lake 5.0.0. Mathlib was pinned to `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all nine dependency revisions were checked. Execution used an isolated, network-disabled environment with a 12 GiB per-process address-space limit and process limit 1024. Pinned dependency object caches were reused: **this was not a rebuild of every dependency from source**.

Nanoda was built from `ammkrn/nanoda_lib` commit `4c544ed4099c8227f07d5de77ad1e69fb0740a27`; executable SHA256: `bd60ccdb0f08f6a1115975c135ec4117dee3a4ff4daab9278f8e9e0d75871d2e`. Its permitted axioms were the three standard axioms above. It checked the target closure, not all of Mathlib or the correctness of the compiler.

**No standalone Lean-kernel replay of all imported proofs was performed.** Nanoda is a separate checker implementation and is not described as such a replay. Trust remains in the pinned compiler/library artifacts, exporter, representation comparator, checker and execution platform. Review and tooling work were conducted within the same Codex project team, with author participation disclosed. These results do not constitute organizer acceptance, a priority determination or an award decision.

## Unmodified original output included

The following five small files are byte-for-byte copies of historical successful-run output, not newly generated or rewritten logs. They are a compact evidence selection, not the entire build transcript or exported proof closure. Nanoda's printed `_` proof bodies reflect its printing configuration; they are not Lean placeholders.

| File | Content | Bytes | SHA256 |
| --- | --- | ---: | --- |
| [finite-theorem.log](logs/finite-theorem.log) | Finite supplier: type, proof body and axioms | 2023 | `4713cc388ec860dcbd4c5b011d9f200fcb79d52ed6e442dc2a86e1349347daa3` |
| [original-question.log](logs/original-question.log) | Separately stated original question: type, proof body and axioms | 4538 | `160c71f8af41857d6b635a633b3e234790bf4bacf1f7bdb400c579fbba0a2e7b` |
| [actual-strings.log](logs/actual-strings.log) | 31 constructor-equality checks with no axioms | 1953 | `79660a2812aa4e3c172f2448e05b43ddf6f87717562a9690040dec727bc7841d` |
| [nanoda-valid.stdout.log](logs/nanoda-valid.stdout.log) | Nanoda success message | 42 | `91ebee6c4641d0271afaeac4d409e146f1ccb6cfad5a555e54748cc2b7992e68` |
| [nanoda-valid.declarations.txt](logs/nanoda-valid.declarations.txt) | All eleven checked target declarations | 5383 | `29f3eed1b2a9137414babd71e9b4da9c61adb0d863c7bd79932ce092c56fc6ee` |

## Historical full-result identities

These SHA256 values identify the original archived stage receipts, checked again when this publication report was prepared. The stage names below are archive identifiers, not links to private machine paths. The complete stage receipts and large exports are not included in this compact evidence selection.

| Historical result | SHA256 |
| --- | --- |
| `lake-clean-03/result.json` | `7206674de8d1ebd7f18f697332cd3ea81b2ec94ebf52c31454497ce9bca017c3` |
| `official-audit-03/result.json` | `ffd15cf8603110b574ed1d852831ca1523a674bb6c693080fbea88a74df006c7` |
| `official-audit-03/output/results/result.json` | `9bd43195471df0fb818ce19fd83c02fc156e369f4192fc75210a8395619c3b11` |
| `raw-export-04/result.json` | `e22975579354e0f829c21c1764ff75be1ecc3e6e7abd7043ffa9b7877572e2f0` |
| `lowered-export-04/result.json` | `6758118e544d078bfff34c0aa8379c065e69d7921d8df41edb17c5e6966bca57` |
| `nanoda-e922-04/result.json` | `38840d9903c45fbb7db5a0e9a01a23228b7a300d4263f9e8b36fdb139fe72391` |

The original export SHA256 was `2e82908cd04b9e48263cb951cab2431fa7772a16ff5d046430ac0caea018db4e`; the checked lowered export SHA256 was `00ae26559fa2f8e5368921eff370ead904878c3b8e315871c19516edfbaea10b`. Earlier failed environment/export attempts were retained separately; they were not overwritten or represented as successful runs.
