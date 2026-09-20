# Provenance and contribution boundary

## Mathematics and inherited formal proof

The hereditary independence-number coloring theorem is due to **Jon H. Folkman**, answering the question of Erdős and Hajnal. Passing from all finite induced subgraphs to an arbitrary graph uses the classical finite-color compactness principle of de Bruijn and Erdős. These are existing mathematical results.

The finite formalization was obtained from **plby/lean-proofs** at the following fixed source:

- Commit: `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
- File: [`src/latest/ErdosProblems/Erdos922.lean`](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos922.lean).
- Original size: 233,944 bytes / 5,605 lines.
- SHA-256: `0bc22004ecbe76ab3cc3f263c29c76994b39017828ea835d987139fa324b9971`.
- Published informal author: Jon Folkman.
- Published formal authors: Codex and GPT-5.6 Sol.

The upstream header identifies Lean and Mathlib 4.33.0. The local port instead uses Lean 4.19.0 and the Mathlib revision in `lake-manifest.json`; the retained header describes the upstream source, not the locally tested toolchain.

The finite proof was split into modules and adapted to the older APIs. The local work therefore includes inherited proof bodies and is not represented as an independent reimplementation of the finite theorem. The finite-subgraph interface also credits the adapted upstream transport arguments, original lines 58–108.

## Work in this package

**Gott-L** initiated the project, selected its objectives and research direction, and led planning. **Codex** performed substantive compatibility proofs and porting, the finite-to-infinite integration, implementation, packaging, and internal reviews and checks.

Local additions include walk and cycle compatibility lemmas, finite-vertex-set and finite-subgraph interfaces, and a compactness proof using Mathlib's Tychonoff and closed-intersection results. `E922InfiniteEndpoint.lean` combines that bridge with the actual finite theorem. Mathlib, Lean, and their contributors retain their own credits and license terms.

`SOURCE-MANIFEST.json` and `source-lock.json` preserve the locked source identities and their preceding local-build provenance. Their paths to earlier workspace materials are historical records, not additional mathematical hypotheses. The 29 proof modules are included in this package. The same-team non-author reviews and automated checks are not described as independent outside peer review.

## Earlier complete extension

[MaxwellLaw's PR #153](https://github.com/TheJustinSunPrize/awards/pull/153), with OpenAI Codex assistance disclosed, already presents the arbitrary-graph theorem and its finite-subgraph equivalences using the same prior finite proof. Its [fixed README](https://github.com/MaxwellLaw/awards/blob/f1af2aeada9c9e5f499b5b69b412d5c4340e23c6/submissions/jsp-000766-MaxwellLaw/README.md) identifies the contribution and reuse boundaries. This is prior complete public work and is acknowledged as such. No first-publication or first-formalization claim is made for the present package.

The local compactness implementation is recorded as locally written; this attribution to PR #153 does not describe its code as copied into this package. PR #153's license for its new files does not relicense the inherited plby finite proof.

## Permission record and historical comments

See [PERMISSION.md](PERMISSION.md) for Gott-L's 2026-09-20 report of specific permission and the limits of the presently recorded evidence. No new standard license is assigned to the inherited source here.

Some retained source comments describe the earlier private-preparation stage, when upstream permission was unverified, or a module's status before final assembly. Those comments are preserved with the checked source bytes. The current package-level permission account is `PERMISSION.md`; the assembled mathematical endpoint and actual local verification are described in [README.md](README.md) and [verification/REPORT.md](verification/REPORT.md). The reference to `tex/922.tex` in the preserved upstream header refers to upstream documentation, not an omitted Lean dependency.
