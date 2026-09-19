# JSP-000847 / Erdős 1017: the Erdős–Goodman–Pósa partition theorem

This packet supplies a complete Lean proof of the classical theorem that every finite simple graph on n vertices has an exact edge partition into at most `floor(n²/4)` single edges and triangles. The mathematical theorem is due to Paul Erdős, A. W. Goodman and Louis Pósa (1966), Theorem 4. The endpoint includes empty graphs and isolated vertices.

This is a known theorem associated with the catalogue question. **It does not solve the open dense-graph improvement asked in Erdős 1017.** The pinned official catalogue records “Eligible to claim: No.” We request assessment of the actual formalization contribution under the applicable rules; this packet asserts neither award entitlement nor a global first-formalization claim.

## Exact result

For any finite simple graph G, the theorem produces a finite family P of vertex sets with all four properties:

1. Every member of P has exactly two or three vertices.
2. Every pair of distinct vertices in a member is adjacent in G.
3. Every edge of G belongs to exactly one member of P.
4. `P.card ≤ (Fintype.card V)^2 / 4`, using natural-number division.

Thus the family is an edge partition. Vertices may occur in several members. No matching, decomposition, positive degree, or lower bound on the number of vertices is assumed in the final theorem.

The main declarations are:

- `EGP.erdos_goodman_posa`: arbitrary finite vertex set and symmetric irreflexive relation.
- `EGP.finite_relation_partition`: all graphs described by an adjacency relation on `Fin n`, with every condition written explicitly.
- `EGP.simple_graph_partition`: the ordinary Mathlib `SimpleGraph` formulation for every finite vertex type.

The intermediate `partition_bound_of_extension` takes a vertex-extension premise. The final declarations discharge it using the fully proved `extend_partition`; it is not an extra assumption in the submitted theorem.

## Proof and source boundary

The proof chooses a minimum-degree vertex and a maximal matching in its neighborhood. Removing the vertex and the matching edges permits induction. Restoring each matching edge as a triangle through the vertex, and each unmatched neighbor as a single edge, yields unique edge ownership. A degree count bounds the number of new parts by `floor(n/2)`, and an exact floor recurrence gives the result.

See [the proof outline](PROOF_OUTLINE.md), [fixed sources and prior work](SOURCES.md), and [the bounded source refresh](prior-art-refresh.md). The inspected PR600 formalization establishes sharpness and related lower bounds; its source explicitly excludes the universal upper bound. Other inspected same-name artifacts leave a theorem admitted, declare it as an additional assumption, or prove a different statement. These bounded observations do not establish global priority. This packet is a new implementation using Mathlib and does not copy code from those projects.

## Reproduction and recorded checks

The project pins Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` in the supplied toolchain and Lake manifest.

```sh
lake update
lake exe cache get Mathlib.Data.Finset.Powerset Mathlib.Data.Finset.Card Mathlib.Data.Finset.Union Mathlib.Data.Finset.Max Mathlib.Data.Fintype.Card Mathlib.Algebra.BigOperators.Group.Finset.Basic Mathlib.Combinatorics.SimpleGraph.Basic Mathlib.Tactic.Linarith Mathlib.Tactic.FinCases Mathlib.Tactic.Ring
python verify.py
```

Use `python3` if appropriate for the platform. The verifier checks the installed Mathlib revision against the pinned revision, copies the seven proof modules into a fresh temporary directory, excludes old project build products, compiles with warnings treated as errors, checks four explicit statements, and audits 25 named declarations. It rejects admitted proofs and nonstandard logical dependencies. The accepted logical dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

The exact source hashes and primary results are in [verification.json](verification.json). A separate internal replay passed all seven modules, eight independently transcribed statement checks and 33 named audits. Its results and reviewer participation are documented in [internal-review.md](internal-review.md) and [review-a/receipt.json](review-a/receipt.json). The reviewer authored the matching module, so this is disclosed internal review, not an independent external human review. Both runs use the pinned Mathlib dependency cache; that cache and the toolchain are trusted rather than rebuilt from bootstrap sources.

## Attribution and licensing

Gott-L initiated and conceived the project, set its objectives, and provided planning and research direction. Codex assistance performed the source research, proof implementation, documentation and internal checks under those instructions. The historical theorem remains attributed to Erdős, Goodman and Pósa; Mathlib retains its own authorship and notices.

Code is licensed under [Apache 2.0](LICENSE); original documentation is licensed under [CC BY 4.0](LICENSE-CONTENT). See [NOTICE](NOTICE). Publication of this packet does not constitute organizer verification, acceptance, an award decision, or payment.
