# Erdős–Goodman–Pósa: partitioning edges into edges and triangles

Copyright 2026. Original documentation for this package, released under CC BY 4.0.

The target is the classical theorem that every finite simple graph with n vertices has a partition of its edges into at most `floor(n²/4)` complete subgraphs, each an edge or a triangle. The mathematical result is due to Erdős, Goodman, and Pósa (1966), Theorem 4; see [SOURCES.md](SOURCES.md).

This document describes the mathematical construction and its Lean representation. It does not attest that final package verification has completed. The work is a new Lean implementation of a known theorem, without a mathematical-discovery or worldwide-first-formalization claim.

## Exact partition semantics

The finite-set theorem works with a finite vertex set S and a symmetric, irreflexive relation R. Its intended conclusion is

```lean
∃ P : Finset (Finset V),
  PartitionOn S R P ∧ P.card ≤ S.card ^ 2 / 4
```

Natural-number division gives the floor in the bound. The definition in `EGPDefs.lean` requires both:

- Every member p of P lies in S, has exactly two or three vertices, and is an R-clique.
- For every R-edge with endpoints in S, exactly one member of P contains both endpoints.

Thus no part contains a nonedge, and every edge has one owner. This is an edge partition; parts may share vertices. The cardinality conditions exclude empty and singleton parts. The uniqueness condition is essential and is stronger than mere edge coverage.

The relation is used in both orientations, but symmetry and the symmetric endpoint-membership condition make the two orientations describe the same undirected edge. Irreflexivity excludes loops. No assumption is imposed on vertices outside S, beyond the relation properties required by the theorem.

## Selecting a vertex and a matching

Induct on the number of vertices, with the relation generalized so that the induction hypothesis also applies after deleting edges.

For nonempty S, choose a vertex v of minimum degree within S. Put `N = neighbors S R v`, `d = N.card`, and `n = S.card`. Then every vertex in N has degree at least d.

Choose a maximal matching M inside N. In the formal representation, M is a finite set of two-element R-cliques whose vertex sets are pairwise disjoint. A cardinality-maximizing matching exists among the finitely many candidate families; adding an edge between two unmatched vertices would contradict its maximality. Consequently, no R-edge joins two unmatched vertices of N.

Write `s = M.card`. The union `covered M` of its endpoints lies in N and has exactly `2s` vertices. These facts follow from the matching definition; they are not assumptions of the final graph theorem.

## The count that makes induction work

The crucial bound is

`d − s ≤ floor(n/2)`.

`EGP.matching_cost_le_half` in `EGPCount.lean` is the corresponding counting lemma.

If every vertex of N is matched, then `d = 2s`. Since `d ≤ n`, the bound follows.

Otherwise choose an unmatched vertex u in N. Every neighbor of u inside N must be matched, or it would form an edge between two unmatched vertices. Therefore

`neighbors S R u ⊆ (S \ N) ∪ covered M`.

The minimum-degree property and this inclusion give

`d ≤ degree(u) ≤ n − d + 2s`.

Rearranging yields `2(d−s) ≤ n`, hence the floor bound. This argument works at all degrees, including degree zero; a separate high-degree case is unnecessary.

The standalone counting lemma accepts the endpoint-cardinality and maximality properties explicitly. `EGPMatching.lean` supplies them from an actual finite matching when the induction is assembled. Its conclusion is not obtained by assuming a matching of the desired size.

## Deleting and restoring the right edges

Remove v from S, and remove the matching edges from the remaining relation. The latter relation is `trim R M`: an R-edge is retained precisely when its two endpoints do not lie together in a member of M. Because every matching member has size two, this deletes exactly the matching edges. Symmetry and irreflexivity are preserved.

Apply the induction hypothesis to this smaller graph, obtaining a partition Q. Restore the removed edges with the family

```text
Q
  ∪ { insert v e : e ∈ M }
  ∪ { {v,u} : u ∈ N \ covered M }.
```

Each matching edge becomes a triangle through v. Each unmatched neighbor contributes a single edge to v. Every old part remains an R-clique, every new triangle is a clique, and each new two-vertex part is an edge.

Coverage separates into three cases: an edge incident to v, a matching edge away from v, or an edge retained by the trimmed relation. These belong respectively to a new part, its matching triangle, or an old part of Q.

Unique ownership is also proved, rather than inferred just from the count. Old parts avoid v and contain no deleted matching edge. Distinct matching triangles cannot share an edge, because the matching edges have disjoint endpoints. A new single edge uses an unmatched vertex, so it belongs to no matching triangle. Two new single-edge parts sharing an edge must be the same part. `extension_partition` expresses this assembly with the actual `PartitionOn` definition.

## Closing the recurrence

At most s triangle parts and `d−2s` single-edge parts are added, for a total of at most `d−s`. Finite unions and images can only lower this cardinality estimate. Hence the resulting partition has at most

`floor((n−1)²/4) + floor(n/2) = floor(n²/4)`

parts. The exact arithmetic identity is proved in `floor_quarter_square_step`, equivalently

`r²/4 + (r+1)/2 = (r+1)²/4`

for natural r. The graph construction and its unique-edge property are established separately from this arithmetic identity.

## Empty graphs and isolated vertices

For an empty vertex set, the empty family is a partition and has size zero. If v is isolated, N and M are empty and the extension adds no part. Thus the induction includes graphs with isolated vertices, edgeless graphs on any number of vertices, and the cases n = 0 and n = 1. It does not assume a positive minimum degree or the existence of an edge.

## Scope and review boundary

This is the historical universal bound associated with JSP-000847 / Erdős 1017. It does not estimate the stronger dense-graph quantity requested when the number of edges exceeds `n²/4`. The pinned catalogue records “Eligible to claim: No”; this package does not change that record or assert an award entitlement.

Gott-L provided project initiation, objectives, planning, and research direction. Codex assistance supplied the implementation, mathematical checks, and original documentation. The authoring workflow for this outline also implemented `EGPCount.lean`; this explanation is not an independent external review. Final compilation and proof-replay evidence must be assessed from the separate verification record.
