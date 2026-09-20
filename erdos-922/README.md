# Erdős 922 / JSP-000766: complete arbitrary-graph formalization

This package contains 29 Lean proof modules establishing the complete natural-number-parameter statement of Erdős Problem 922, including arbitrary, possibly infinite graphs. It combines an attributed Lean 4.19 port of the existing finite Folkman proof with locally written compatibility lemmas, finite-subgraph interfaces, and a finite-color compactness argument.

Gott-L initiated the project, set its objectives and research direction, and led planning. Codex carried out the substantive porting, integration, implementation, and internal checks. The mathematics is Folkman's known theorem; the inherited finite formalization and earlier public arbitrary-graph implementation retain their credits. **No mathematical discovery, first-formalization priority, official acceptance, or award is claimed.** See [PROVENANCE.md](PROVENANCE.md) and [PERMISSION.md](PERMISSION.md).

This publication copy is prepared for the branch `codex/erdos-922-complete`. That branch name is a publication plan, not a claim that this copy has already been published or accepted.

## Complete statement

For every natural number `k` and every simple graph `G` on any vertex type, suppose that each finite vertex set `S` contains an independent subset `I` with

```text
I ⊆ S                 |S| ≤ 2|I| + k.
```

Then `G` has a proper coloring with `k + 2` colors. There is no finiteness, countability, local-finiteness, or nonemptiness assumption on the ambient graph. The case `k = 0` is included. The integral inequality avoids truncated natural-number subtraction.

[E922InfiniteEndpoint.lean](src/E922InfiniteEndpoint.lean) exports:

- `Erdos922Adapter.colorable_of_largeIndependentFinsets`;
- `Erdos922Adapter.chromaticNumber_le_of_largeIndependentFiniteSubgraphs`;
- `Erdos922.erdos_922_arbitrary`.

The finite-subgraph formulation allows edge deletion and is proved equivalent to the finite-vertex-set formulation. The final theorem uses the proved finite Folkman theorem; it does not assume that theorem or a minimal-counterexample exclusion as an extra premise.

## Reproduce the project

Install Python 3 and Lean through `elan`. The project fixes Lean `v4.19.0`, Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, and all nine Lake dependency revisions. Run these commands from this directory without changing those pins:

```sh
python verify-layout.py
lake exe cache get
lake build
lake env lean -t 0 -DwarningAsError=true audit/E922ProjectRebuildAudit.lean
```

`verify-layout.py` checks the locked proof and audit bytes and local import closure; it does not run Lean. The build targets include every proof module and the original audit. The audit prints theorem types and axiom dependencies. Dependency-cache retrieval requires network access; the proof build uses the pinned dependencies.

## Actual verification and its limits

The unchanged proof/configuration originated at local commit `b1edf8873a1a01edebbf2a12c56276223e1cbb4b`. The recorded local run rebuilt all 29 proof modules and the original audit, checked 11 designated targets with 35 successful audit commands, and completed a separate statement-equivalence check. The external Nanoda run checked 10,884 declarations successfully; both deliberately invalid controls were rejected for their expected reasons. See [the verification report](verification/REPORT.md) for the exact inputs, evidence, and trust boundary.

These are completed local checks, not an organizer's acceptance or an external human review. Compatible independent Lean kernel replay was not executed. Pinned dependency caches were reused. The reported successful checks belong to the identified proof bytes; this documentation update is not a claim that a new public commit has received a new full verification run.

## Permission and prior work

On 2026-09-20, Gott-L reported that he had asked plby about permission for this E922 work and received an affirmative reply. The original reply or link is awaiting inclusion in the record. This is recorded as **user-reported, source-specific permission**, not as an MIT, Apache, or unrestricted sublicensing grant. [PERMISSION.md](PERMISSION.md) states the evidence boundary.

The earlier [PR #153](https://github.com/TheJustinSunPrize/awards/pull/153) already presents a complete arbitrary-graph extension based on the same upstream finite theorem. It is explicitly acknowledged; this package does not claim to be the first complete formalization.
