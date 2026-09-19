# JSP-000904 / Erdős 1087: exact distance-counting identities

This packet formalizes the finite counting reduction in [haipapa123's PR 586](https://github.com/TheJustinSunPrize/awards/pull/586), including the universal planar multiplicity bound. The objects are actual finite sets of points, unordered edges and ordered distance quadruples. The counting equalities are proved from these objects, rather than assumed.

## Completed mathematical scope

For a finite set P of distinct planar points, let n be its cardinality. An edge is an unordered two-point subset. An equal-edge pair consists of two different edges of equal length, with the pair itself unordered.

- F counts four-point subsets containing an equal-edge pair.
- W sums the number of equal-edge pairs over every four-point subset.
- T counts equal-edge pairs sharing a vertex. The intersection of their edges is proved to be a singleton, so this is the distinguished-apex isosceles count, including collinear midpoint configurations.
- B counts equal-edge pairs with four distinct endpoints.
- Q counts ordered quadruples (a,b,c,d) from P with `distance(a,b)=distance(c,d)>0`. Points can repeat across the two edges.

The general incidence and orientation theorems give

```text
W = B + (n-3) T
Q = 2 n (n-1) + 8 (T+B)
```

For n≥4, their combined form is

```text
8 W + 2 n (n-1) = Q + 8 (n-4) T.
```

The planar geometric argument gives

```text
F ≤ W ≤ 10 F.
```

The factor 10 is attained by the explicitly checked set
`{(0,0), (2,0), (3,sqrt(3)), (1,sqrt(3))}`: it has four points, F=1 and W=10.

The subtraction in the combined natural-number identity is used only with n≥4. The support incidence identity itself is valid for every finite set, including empty and small sets.

**This is a formalization of the exact finite-counting reduction. It does not prove the open `f(n)≤n^(3+o(1))` conjecture, the general isosceles bound, or the Guth–Katz and Katz–Tardos estimates.** No unfinished source theorem or custom mathematical assumption is imported to supply those conclusions.

## Meaning of the definitions

The plane is represented by pairs of real coordinates. `planeDistance` is the ordinary Euclidean formula, the square root of the sum of squared coordinate differences. `planeQuadruples` uses equality and strict positivity of that distance directly.

For unordered edges, `planeColor` sums squared distances over their ordered endpoint pairs. Its value on `{a,b}` is proved to be twice the squared Euclidean distance. Thus it has exactly the same equality classes as ordinary edge lengths. The factor of two does not alter F, W, T or B.

`four_set_degenerate_iff` proves that positive weight is equivalent to fewer than six distinct edge colors on a four-point set. `planeEdgeLength_pair` identifies the unordered edge length with ordinary Euclidean distance, and `planar_degenerate_iff` proves the same fewer-than-six statement for those ordinary lengths. `triangle_pair_unique_apex` proves that the shared vertex in T is unique. T uses this shared-edge-pair encoding; there is no separate apex/base-product representation in the implementation. `planeQuadruples_eq` connects the positive Euclidean-distance definition to the orientation-counting theorem.

## Proof architecture

| Source | Proved role |
| --- | --- |
| E1087Core.lean | Exact finite objects and support partition into three or four points |
| E1087Incidence.lean | Containing four-set counts, double counting, and weighted/unweighted comparison principles |
| E1087Meaning.lean | Repeated-edge/fewer-than-six equivalence and unique shared apex |
| E1087Quadruples.lean | Two orientations per edge, four orientation choices per ordered edge pair, and the factor-eight identity |
| E1087ColorBound.lean | Six objects with at least two colors have at most ten monochromatic pairs |
| E1087Plane.lean | Four distinct planar points cannot be equidistant; planar multiplicity bound and exact sharpness example |
| E1087.lean | Euclidean-distance correspondence, assembled universal endpoints, and W=10,F=1 sharpness |

The geometric obstruction uses an explicit two-dimensional Gram determinant identity, proved by polynomial arithmetic. If all six squared distances were the same positive number, the same determinant would be positive, contradicting the identity. The combinatorial bound counts at least five cross-color pairs among the fifteen pairs of six edges.

## Attribution and prior work

The mathematical reduction and exposition being formalized are credited to **haipapa123's submission**, [fixed commit daa68321eca18b869069e5cdec51ab5526d57558](https://github.com/haipapa123/awards/blob/daa68321eca18b869069e5cdec51ab5526d57558/docs/submissions/jsp-000904-distance-counting/PROOF.md). That submission discloses ChatGPT/Codex assistance. Its documentation is CC BY 4.0; this packet is a new Lean implementation and an adapted explanation, with attribution retained. It does not imply endorsement by the original contributor.

Gott-L initiated this project, set its goals and research direction, and owns and authorizes this submission. Codex performed the research, formal proof development, implementation, documentation and internal checks. Project planning is not presented as discovery of another contributor's mathematical argument.

The bounded prior-source review found the five files in PR 586 contain a written proof and finite checker, but no Lean proof. Formal Conjectures PR 5859 supplies proposed definitions with the research theorems unfinished. Other inspected sources do not provide this exact counting theorem. Details and search limits are in [prior-review.md](prior-review.md). This is not a global first-priority certificate or an award decision.

## Reproduction and verification

Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned, including transitive dependency revisions in `lake-manifest.json`.

```text
lake exe cache get Mathlib.Data.Finset.Powerset Mathlib.Data.Finset.Card Mathlib.Data.Finset.Prod Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Algebra.BigOperators.Ring.Finset Mathlib.Data.Real.Sqrt Mathlib.Tactic.Ring Mathlib.Tactic.Linarith
python verify.py
```

Preserve the supplied dependency manifest; if Lake changes a pinned revision, the verifier rejects it. `verify.py` copies the local proof sources to a fresh directory, excludes old local build products, compiles with warnings as errors, checks the explicit types in `TypedAudit.lean`, and audits named declarations. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. The pinned dependency caches remain part of the trusted environment and are not rebuilt by this check.

All seven proof modules passed fresh compilation with warnings treated as errors. All 54 named declaration audits and seven explicit definition/endpoint checks passed. The source hashes and actual results are in [verification.json](verification.json); the checked type statements are in [TypedAudit.lean](TypedAudit.lean).

The internal reviews distinguish proof authorship, source correspondence review and fresh replay. They are not official prize verification, independent human review, or a second implementation of the Lean kernel. The geometric source review also records the shared-edge-pair representation of T explicitly.

A separate same-team agent that did not write the seven proof modules also freshly compiled all seven, checked 15 independently transcribed statements, and audited 78 public proof declarations plus those 15 review statements (93 named audits). All passed. See [internal-review.md](internal-review.md), [review-a/receipt.json](review-a/receipt.json), [review-a/Audit.lean](review-a/Audit.lean), [review-a/AxiomAudit.lean](review-a/AxiomAudit.lean), and [geometry-review.md](geometry-review.md) for the actual evidence and limits.

## License

Independently written proof code and scripts: Apache-2.0. Explanatory documentation: CC BY 4.0, retaining the credited source's attribution. See LICENSE-CODE, LICENSE-CONTENT and NOTICE. Dependencies keep their own licenses. Private contact and payment information is excluded.
