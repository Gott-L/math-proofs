# Sources, attribution, and bounded source audit

Copyright 2026. Original documentation for this package, released under CC BY 4.0.

This package implements a known finite graph theorem. Its mathematical attribution is to Erdős, Goodman, and Pósa. The project does not claim a new mathematical discovery or establish worldwide formalization priority. No Lean code from the prior E1017 projects listed below was copied into this implementation; they were inspected to determine scope and avoid mistaking a related result, an admitted statement, or an axiom for the target proof.

## Original mathematical theorem

P. Erdős, A. W. Goodman, and L. Pósa, **The representation of a graph by set intersections**, Canadian Journal of Mathematics **18** (1966), 106–112. [DOI](https://doi.org/10.4153/CJM-1966-014-3), [publisher PDF](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/C1EC0B9CD0270564F05B5A62301BE20D/S0008414X00040104a.pdf/the-representation-of-a-graph-by-set-intersections.pdf).

The relevant result is **Theorem 4**, on pp. 108–109: the edge-disjoint refinement using only edges and triangles. Theorem 2 gives a covering result and does not alone supply unique edge ownership. This implementation expresses the Theorem 4 induction using a maximal matching in a minimum-degree neighborhood. Empty graphs and isolated vertices are included in the finite-set formulation. The statement and proof were read; this documentation provides its own explanation of the Lean construction rather than reproducing the paper's prose.

## Catalogue scope

The inspected [JSP-000847 catalogue entry](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0801-0900.md#JSP-000847) is pinned to `TheJustinSunPrize/awards@f4e7173d89dfe91022a185427d63452c8ffbf6ae`. It records Progress, Lean proof No, and Eligible to claim No.

Its broader problem concerns clique partitions of dense graphs. The universal historical bound targeted here is a scoped known component, not the unresolved improvement requested for edge counts above `n²/4`. The catalogue labels do not establish recognition of this package or an entitlement to payment.

## PR600: a complementary sharpness result

[Official PR600](https://github.com/TheJustinSunPrize/awards/pull/600) was inspected at head `7c0d54e586222713803912b9f2007bf4d4266670` in `CollinYuanjieRen/awards`:

- [Proof.lean](https://github.com/CollinYuanjieRen/awards/blob/7c0d54e586222713803912b9f2007bf4d4266670/submissions/jsp-000847-cyr/Proof.lean).
- [Proof/Defs.lean](https://github.com/CollinYuanjieRen/awards/blob/7c0d54e586222713803912b9f2007bf4d4266670/submissions/jsp-000847-cyr/Proof/Defs.lean).
- [Proof/Main.lean](https://github.com/CollinYuanjieRen/awards/blob/7c0d54e586222713803912b9f2007bf4d4266670/submissions/jsp-000847-cyr/Proof/Main.lean).

The definitions require unique edge ownership. Its proved results include the trivial edge-count upper bound, the triangle-free equality case, and balanced-bipartite sharpness. In particular, `sq_div_four_le_f` is the lower bound at the balanced-bipartite edge count. Its README expressly excludes the universal EGP upper bound and the edges-and-triangles refinement. The source audit found no hidden universal construction in its proof closure. That package's own replay was not rerun here, and its code is not reused.

## Formal Conjectures PR5868: a statement, not this proof

[PR5868](https://github.com/google-deepmind/formal-conjectures/pull/5868) was inspected at `stantheman0128/formal-conjectures@193978cfb011f817d760f9cd5259d42061dccd5b`. Its [ErdosProblems/1017.lean](https://github.com/stantheman0128/formal-conjectures/blob/193978cfb011f817d760f9cd5259d42061dccd5b/FormalConjectures/ErdosProblems/1017.lean) describes f using `SimpleGraph.IsDecomposition` and leaves the dense-graph estimation target admitted with `answer(sorry)` and `sorry`.

The inspected file supplies no EGP proof or variant. It is evidence about that pinned PR source, not a claim that the file was merged or that every later Formal Conjectures revision was searched. It is not imported by this package.

## lean-genius: an assumed theorem and a weaker partition structure

The inspected revision is `rjwalters/lean-genius@dc62f771ed5010abfdb04247dff6143e0e69d3e7`.

[`Erdos1017Problem.lean`](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos1017Problem.lean) imports [`Erdos1017OQ01.lean`](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos1017OQ01.lean). In OQ01, `egp_theorem` is an `axiom`; `cliquePartitionNum_le_turan` invokes it. Its `EdgeCliquePartition` structure requires coverage without unique ownership. Consequently it does not supply an unconditional proof of the exact partition theorem represented here.

The inspected OQ02, OQ03, and OQ03OQ01 files supply arithmetic around the bound; OQ04 and OQ05 develop related cover/partition frameworks. They do not fill this missing construction. The separately inspected [`Erdos719Problem.lean`](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos719Problem.lean) assumes the needed graph decomposition in `graph_case_bound`. These are source-reading conclusions, not results of rebuilding those projects.

## Additional bounded checks

At `ryantuck/erdos-ai@891f30e7993a0d74442ede619ce3d07f4caecccb`, the inspected [1017 variant](https://github.com/ryantuck/erdos-ai/blob/891f30e7993a0d74442ede619ce3d07f4caecccb/deepmind/deepmind/1017.lean) and its inspected copies leave EGP admitted. The [daedalus stub](https://github.com/daedalus/alphaproof-nexus/blob/4e65a6ca81655f090a3c8dcf9f56e4a38c984f4c/problems/erdos/1017/Erdos1017.lean), at `4e65a6ca81655f090a3c8dcf9f56e4a38c984f4c`, contains no proof.

These checks did not locate an unconditional proof matching the proposed endpoint in the artifacts read. They are not an exhaustive search of all repositories or later revisions. No third-party project was replayed as part of this documentation task.

## Implementation, dependencies, and roles

The new implementation uses Lean 4.19.0 and Mathlib commit [`c44e0c8ee63ca166450922a373c7409c5d26b00b`](https://github.com/leanprover-community/mathlib4/tree/c44e0c8ee63ca166450922a373c7409c5d26b00b). Mathlib's finite-set, cardinality, ordering, and elementary arithmetic infrastructure retains its own authorship and Apache-2.0 licensing.

Gott-L: project initiation, objectives, planning, and research direction. Codex assistance: implementation, mathematical checks, and original documentation. The mathematical theorem remains attributed to Erdős, Goodman, and Pósa. The writer of these notes participated in the proof development, including the counting module, and is not an independent external reviewer.

This source record does not assert completed final verification, organizer acceptance, eligibility, a prize amount, or priority. Those matters must not be inferred from the existence of these documentation files.
