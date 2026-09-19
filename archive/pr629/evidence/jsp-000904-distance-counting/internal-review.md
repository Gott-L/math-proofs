# Internal source and semantic review of the Erdős 1087 packet

Review completed on 17 September 2026. The seven frozen proof modules passed a separate fresh compilation, 15 explicit statement checks, and 93 named axiom checks: 78 public proof definitions/theorems and 15 review statements. No mathematical or statement-correspondence defect was found in the scope below.

This review was performed by a separate Codex agent on the same project team. That agent did not write any of the seven proof modules. It did contribute earlier research and environment preparation, and wrote these review statements and this report. This is an internal AI cross-check, not an official prize review, independent human review, or a separate implementation of Lean's kernel.

## Source and scope

The mathematical source checked was [haipapa123's PR 586 proof note at commit daa68321eca18b869069e5cdec51ab5526d57558](https://github.com/haipapa123/awards/blob/daa68321eca18b869069e5cdec51ab5526d57558/docs/submissions/jsp-000904-distance-counting/PROOF.md). Its attribution and CC BY 4.0 license must remain visible. This packet formalizes the note's exact finite counting identities, the planar multiplicity bound, and its sharpness example.

It does **not** prove the open asymptotic assertion in Erdős 1087, a new general bound on isosceles triangles, or the external Guth–Katz/Katz–Tardos estimates. None of those results is silently supplied as a hypothesis of the assembled finite-counting endpoints. This review makes no first-priority or award-eligibility claim.

The review covered all seven source files, including the bodies of the incidence and orientation counting arguments and the planar geometric obstruction. The corresponding publication declarations were checked against the actual definitions, rather than accepted from theorem names.

## Definitions and exact counting

`P` is a `Finset`, so its points are distinct as set elements. An edge is a two-element subset of `P`. `equalPairs` contains two-element sets of different edges of the same color. Both the edges and their pairing are unordered. It excludes repeated copies of one edge without choosing an orientation. Its support is the union of the two edges.

Two different two-element edges have support size three or four. The code proves this dichotomy, partitions `equalPairs` accordingly, and defines the counts T and B from those two parts. There is no assumption that all equal-edge pairs fall into the desired cases.

For support of size three, containing four-element subsets are in bijection with the points outside the support. There are `n-3` such subsets. A support of size four has exactly one containing four-element subset. `totalWeight_as_support_sum` then interchanges the actual incidence sums. Consequently `totalWeight_identity` proves

```text
W = B + (n-3) T
```

for every finite set and every edge-color function. It does not take this identity, a per-support count, or any geometric restriction as an input. Natural subtraction causes no problem for small sets: a three-point support requires at least three points, and its coefficient is zero at n=3. There are no four-subsets when n<4.

`triangle_pair_unique_apex` proves that the two edges counted by T have a singleton intersection. Thus this encoding is equivalent to choosing an apex and an unordered pair of distinct base points at equal distances from it. Collinear midpoint configurations are included. The implementation uses the shared-edge-pair representation; it does not separately formalize a cardinality theorem for an apex/base-product representation. The singleton-intersection result and the explicit edge definitions justify the interpretation without an extra factor of two.

The ordered quadruple argument also counts concrete finite fibers. Each unordered edge has two orientations. An ordered pair of edges therefore has four orientation choices. Equal ordered edge pairs split into the diagonal and two orderings of each pair of different equal-colored edges. This proves the four/eight coefficients, rather than assuming them. The diagonal contributes `4 * choose(n,2) = 2*n*(n-1)`. Hence

```text
Q = 2 n (n-1) + 8 (T+B).
```

The generic orientation theorem assumes only that the supplied unordered-edge color agrees with the supplied ordered-pair value on a nondegenerate edge. The final planar theorem discharges that compatibility from `planeColor_pair`.

## Ordinary Euclidean meaning

The coordinate type is `Real × Real`. The formalization defines the ordinary Euclidean distance explicitly as

```text
sqrt((x₁-y₁)² + (x₂-y₂)²).
```

This is important: the proof does not accidentally use the default product metric on this type. `planeQuadruples` uses equality and strict positivity of this explicit distance. Points may repeat across the two edges. Positive distance excludes a repeated endpoint within either edge; equality supplies positivity for the second edge as well. The proof of `planeQuadruples_eq` checks both directions.

On `{a,b}`, with `a != b`, `planeColor` is twice the squared Euclidean distance. Nonnegativity and injectivity of the square root on nonnegative arguments show that the color classes are exactly the classes of ordinary edge lengths. `planeEdgeLength_pair` also identifies the unordered edge-length function directly with the displayed coordinate formula.

For four-point sets, the code proves that positive weight is equivalent to fewer than six distinct edge colors. `planar_degenerate_iff` transfers this to fewer than six ordinary Euclidean lengths. The review adds a checked `raw_bad_count` statement: F is literally the cardinality of the filter of four-subsets whose six ordinary edge lengths have image cardinality below six. Thus the final comparison applies to the mathematical bad-set count, not merely an unexplained color predicate.

## The planar bound and sharpness

The geometric step proves that four distinct planar points cannot have all six distances equal. Three displacement vectors in two coordinates satisfy an explicit Gram-determinant polynomial identity. Equal positive squared distances would give Gram diagonal entries rho and off-diagonal entries rho/2, forcing a positive determinant and a contradiction. This proof depends on the two-dimensional coordinate calculation and positivity, not on an unproved equidistance theorem.

For six edges with at least two colors, choose a nonempty color class and its nonempty complement. Their cross pairs are distinct, non-monochromatic, and number at least five. Among all fifteen pairs, at most ten can therefore be monochromatic. The planar argument supplies the required nonconstant coloring. This establishes the pointwise weight bound for every four-point subset. Summing it, and using that every positive integer weight is at least one, yields

```text
F <= W <= 10 F.
```

The exact witness is `{(0,0), (2,0), (3,sqrt(3)), (1,sqrt(3))}`. Its four points are proved distinct. Five edges have squared length four; the remaining edge has squared length twelve. The formal proof verifies the five equal-colored edges, obtains ten equal-edge pairs, and combines this lower bound with the universal upper bound. The final statement checks cardinality four, F=1, and W=10. It uses exact square-root identities, not floating-point evaluation.

The combined weighted identity is stated only when `4 <= n`, so the conversion between `n-3` and `n-4+1` is valid in natural-number arithmetic. The Q identity and comparison themselves hold for every finite planar set, including empty and small sets.

## Separate replay and explicit statement checks

The checked review source is [review-a/Audit.lean](review-a/Audit.lean). It contains 15 statements: the layers of the edge/pair/support/W/T/B definitions, the general incidence identity, the raw Euclidean distance formula, its unordered-edge counterpart, Q with its complete ordered positive-distance predicate written out, the ordinary-distance bad-set count, the resulting comparison, the weighted identity, and sharpness. Layer-by-layer definitional equalities connect W, T and B to their literal finite-set constructions. This approach avoids hiding a replacement definition inside a theorem abbreviation.

The seven source modules were copied byte-for-byte to a newly created directory and compiled in dependency order. The import path contained that new output directory and the nine pinned dependency library directories; it excluded the project's existing local build-output directory. No old local E1087 `.olean` was used. Compilation used Lean 4.19.0, stack setting `-s 65536`, and `-DwarningAsError=true`. Each source, the review source, and the generated [review-a/AxiomAudit.lean](review-a/AxiomAudit.lean) exited successfully without warnings.

The dependency environment used Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Its existing dependency caches were reused; this review did not rebuild or independently validate the entire Mathlib dependency graph. The same Lean kernel and pinned libraries remain part of the trusted environment.

All 93 requested axiom reports were present and parsed. Every dependency was in the allowlist `propext`, `Classical.choice`, `Quot.sound`. A separate source scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, or `unsafe` occurrence in the seven proof modules. The named public endpoint audits also cover the private helper proofs used by those endpoints through their dependencies.

The successful, path-sanitized [review-a/receipt.json](review-a/receipt.json) records actual commands, exit codes, outputs, hashes, declaration names, statement checks and import-isolation properties. The proof-source hashes were checked again after replay and were unchanged. Failed drafts of review-only statements are not presented as successful evidence.

## Reviewed source hashes

| File | SHA-256 |
| --- | --- |
| E1087Core.lean | `1783d6e17ef631c53e9c5b25e7eca942ee7fdb6060de74f228f230faa0fbca93` |
| E1087Incidence.lean | `3049c4c84be80d60165db2eb63ef3a41854c719457850811472bca3bd428f72d` |
| E1087Meaning.lean | `26be44f15eec860114d4450bf7566086d37bfd40c5d4ec0c081a6abb32f622c4` |
| E1087Quadruples.lean | `973e50feed0566a47defee98395deb920cb6898b3343c7ec59ac778cc7a3520f` |
| E1087ColorBound.lean | `8d59e494d1f758ffc67363a016e69505ea53dbbbec889320710fc02ba1604e99` |
| E1087Plane.lean | `d668c0ba61586265042db353ae8e21e448e3dede572c0e1e43fe02ee03a8d369` |
| E1087.lean | `be084ab346910c57f5b11e2c0c7028a31b2ba8e69d6949c556687b6bfbf462af` |

Documentation in this review is CC BY 4.0, with the mathematical-source attribution above retained. The review Lean files are Apache-2.0.
