# Internal semantic review and fresh replay

Original review documentation, copyright 2026, licensed under CC BY 4.0; see `LICENSE-CONTENT`. The Lean review sources are licensed under Apache-2.0.

The reviewed package proves the classical Erdős–Goodman–Pósa edge-partition bound: every finite simple graph on n vertices admits a partition of its edges into at most floor(n²/4) parts, each a single edge or a triangle. No mathematical defect or remaining proof premise was found in the assembled endpoints. This is a formalization of a known theorem, not a solution of the stronger dense-graph improvement in Erdős problem 1017. The catalogue status and bounded prior-source search described in `SOURCES.md` do not establish priority or prize eligibility.

The reviewer authored `EGPMatching.lean` and participated in the same AI-assisted project. The other six proof modules were written by other agents. Accordingly, this report is an internal cross-module semantic review and a separately executed replay, not external human, official, or wholly independent authorship review.

## Exact statement checked

The eight statements in [`review-a/Audit.lean`](review-a/Audit.lean) were written separately from the primary verifier's four endpoint checks. They expand the clique and partition definitions, restate the finite-set, `Fin n`, and `SimpleGraph` endpoints, expand unique ownership, exclude a shared edge between different parts, and check the exact floor recurrence.

For an arbitrary finite set S and any symmetric, irreflexive relation R, the final result produces a finite family P such that:

- Every part lies in S, has exactly two or three vertices, and every pair of distinct vertices in that part is related by R.
- Every related pair in S lies in exactly one part of P.
- The number of parts is at most `S.card ^ 2 / 4`, using natural-number division.

The clique condition excludes additional nonedges, and the unique-existence condition establishes an edge partition rather than only an edge cover. Distinct parts can share a vertex; they cannot share two distinct vertices. Isolated vertices need not belong to any part. The separate `explicit_unique_ownership` and `different_parts_no_common_edge` checks verify these consequences directly.

The three final theorems are `EGP.erdos_goodman_posa`, `EGP.finite_relation_partition`, and `EGP.simple_graph_partition`. Their independently transcribed statements contain no matching assumption, no extension assumption, no positive minimum-degree assumption, and no unmentioned restriction to nonempty graphs. The first permits any ambient vertex type and a finite S; the third requires only a finite vertex type and a `SimpleGraph`. Empty graphs, singleton graphs, and edgeless graphs are included.

## Proof and assumption review

The matching module selects a largest matching from a finite powerset. Its members are disjoint two-vertex cliques in the neighborhood N. The covered set is proved to lie in N and to have exactly twice the matching's cardinality. If two uncovered vertices were adjacent, symmetry and irreflexivity make their pair a new disjoint matching edge, contradicting maximal cardinality. Thus the absence of such an edge is proved, not an input to the final theorem.

Write n for the current number of vertices, d for the degree of a minimum-degree vertex v, and m for the number of matching edges in its neighborhood. In the fully covered case, d=2m gives d−m≤floor(n/2). Otherwise an uncovered neighbor u has every neighbor either outside N or in the matching's covered set. The source proves this set containment before taking cardinalities. Minimum degree then gives d≤degree(u)≤n−d+2m, hence d−m≤floor(n/2). The proved inequality 2m≤d justifies every natural subtraction used in this argument and in the extension count.

The assembly module removes v and the matching edges, recursively partitions the remaining relation, and adds a triangle for each matching edge and a single edge from v to each uncovered neighbor. All parts are proved to be cliques of the required size. Unique coverage is checked across the six possible pairs of old parts, added triangles, and added single edges. In particular, old parts cannot contain a removed matching edge; different matching edges cannot share a vertex; and an uncovered neighbor cannot lie in a matching edge. These arguments discharge the uniqueness requirement rather than merely counting a cover.

The extension cardinality is at most the old cardinality plus m+(d−2m)=d−m. Union and image cardinality inequalities suffice; no unproved injectivity assumption is used. Strong induction is generalized over R, so it can be applied to the trimmed relation on `S.erase v`. Symmetry and irreflexivity are proved to survive trimming. The exact natural-number identity

```text
n² / 4 + (n+1) / 2 = (n+1)² / 4
```

supplies the induction step, with both parity cases proved and the empty case handled separately.

`partition_bound_of_extension` intentionally has an extension theorem parameter as an intermediate modular statement. The final theorem explicitly instantiates it with the closed, proved `extend_partition`. The raw endpoint checks confirm that this parameter does not remain in any published final endpoint. The earlier preliminary `review-a-notes.md` completion obligation is therefore discharged.

## Replay and trust boundary

The separate replay completed on 2026-09-17 at the time recorded in [`review-a/receipt.json`](review-a/receipt.json). All seven source modules were copied byte-for-byte into a fresh directory and compiled in dependency order using Lean 4.19.0, stack setting 65536, and warnings treated as errors. The existing project build directory was excluded from the import path. Both review modules were then compiled against those fresh outputs. All nine invocations exited successfully.

The replay audited all 25 public source declarations and all eight review declarations through [`review-a/AxiomAudit.lean`](review-a/AxiomAudit.lean). Every one of the 33 reports contains only a subset of `propext`, `Classical.choice`, and `Quot.sound`. In particular, all three final endpoints depend only on those standard axioms. No admitted proof or custom mathematical axiom is present in the audited dependency closures.

The nine dependency repository revisions were checked against the supplied manifest, including Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Existing compiled dependency caches were reused; this review does not claim to rebuild Mathlib, its dependencies, or Lean from source. It also does not certify the entire compiler/runtime or external publication process. The receipt records command arguments, return codes, outputs, versions, dependency revisions, and SHA-256 hashes using relative source names without private contact data or local absolute paths.

The source hashes were checked again after the replay and were unchanged:

| Source | SHA-256 |
| --- | --- |
| `EGPDefs.lean` | `5bc5b0bbf86a9b7ec5190506b7e2321346cf473626c73f667967eed04b92172d` |
| `EGPMatching.lean` | `4d30d8cac81e7c0e6498a8e4b83cb1642f92b7850a84186301ee779e191924be` |
| `EGPCount.lean` | `01926ef2e82a503efa3d02548542d92d40859f828fa8969ad315afccc7846705` |
| `EGPAssembly.lean` | `da14d96c35ec136f2bdc32c24310e85779840cfa98a39a1cbf47737d3df89632` |
| `EGPInduction.lean` | `ffaca4ae050eb34a082f5a98d62847ee0ad80989d3b74414ae18fb7d9cc98dbe` |
| `EGPSubmission.lean` | `2d8aacaf2a234dc46e760e5432a33ce8a931e17d4e5294bb21b5cf104d2e7ea3` |
| `EGPGraph.lean` | `e1281125a3be76ad48b04d7a721be8bb02f4687b3a6fa97c572440ad76689188` |

The README's mathematical scope and its distinction between the primary verification receipt and this internal review agree with the inspected sources. The known mathematical attribution is Erdős, Goodman, and Pósa, *The representation of a graph by set intersections*, Theorem 4 (1966), [DOI](https://doi.org/10.4153/CJM-1966-014-3). The packet does not prove the stronger open dense-graph statement, assert a first formalization, or establish an award entitlement.
