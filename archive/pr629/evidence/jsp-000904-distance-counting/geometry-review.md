# Geometry and statement-correspondence review

Review date: 2026-09-17.

This is an internal source and mathematical review. The reviewer did not author `E1087ColorBound.lean`, `E1087Plane.lean`, `E1087Meaning.lean`, `E1087Incidence.lean`, or the assembled `E1087.lean`. The reviewer **did author `E1087Quadruples.lean`** within the same collaborating team. Accordingly, this is not an independent external attestation of the whole package. In particular, the orientation-counting module was not reviewed by a disinterested third party here.

The reviewed mathematical source is [haipapa123's PR 586](https://github.com/TheJustinSunPrize/awards/pull/586), specifically [PROOF.md at commit daa68321eca18b869069e5cdec51ab5526d57558](https://github.com/haipapa123/awards/blob/daa68321eca18b869069e5cdec51ab5526d57558/docs/submissions/jsp-000904-distance-counting/PROOF.md) and its [statement map](https://github.com/haipapa123/awards/blob/daa68321eca18b869069e5cdec51ab5526d57558/docs/submissions/jsp-000904-distance-counting/STATEMENT_MAP.md). The source's mathematical attribution and disclosed AI assistance are retained. This review makes no priority, recipient, acceptance, or award claim.

## Finding

No mathematical defect requiring a change to the reviewed universal geometry or counting statements was found. In particular:

- The development uses the Euclidean distance formula explicitly. It does not accidentally use the default product metric on `ℝ × ℝ`.
- The impossibility of four equidistant planar points is proved from an explicit polynomial identity and a strictly positive squared distance.
- The bound of ten equal-edge pairs is derived from actual six-element sets and a proved geometric obstruction.
- F, W, T, B and Q are cardinalities or sums over explicitly defined finite objects. The two counting identities are not hypotheses supplied to the final theorem.
- The ordinary edge-length interpretation of F and the positive-distance interpretation of Q have explicit proved bridges.
- T uses the unordered-edge-pair representation described below. This is not an arbitrary assumed numerical T, but a separate literal apex/base-set cardinality has not been introduced and equated by a formal bijection.

This review did not rerun the complete build, fresh source replay, or final axiom audit. Those checks are assigned to the package's separate replay and verification process; their actual results must be reported by that process. The sharpness additions were still being finalized during this review.

## Euclidean coordinates versus the default product metric

`Plane` abbreviates `ℝ × ℝ`. That type's default metric is the product sup metric, so using the unqualified function `dist` would require care. The relevant code instead defines

```text
sqDist(x,y) = (x.1-y.1)^2 + (x.2-y.2)^2
planeDistance(x,y) = sqrt(sqDist(x,y)).
```

These formulas give the ordinary Euclidean distance. No identification of `planeDistance` with the product type's default `dist` is made or needed. A source scan of the E1087 Lean modules found no call to `dist`, `edist`, or `norm` supplying the geometric meaning.

The distinction matters mathematically: the four corners of the unit square are pairwise equidistant in the sup metric, which would allow all fifteen edge pairs to be monochromatic. They are not pairwise equidistant in the Euclidean metric. The implementation avoids this failure by using the displayed formula throughout.

`sqDist_pos` proves positivity for distinct points directly from the two coordinate squares. `sqDist_nonneg` proves nonnegativity for arbitrary points. Consequently `planeDistance_pos_iff` proves strict positivity exactly when the points differ, and `planeDistance_eq_iff` uses square-root injectivity only with verified nonnegative arguments.

## Colors and ordinary unordered edge lengths

`planeColor e` is the sum of `sqDist x y` over both ordered endpoints in the finite set e. The theorem `planeColor_pair` proves

```text
planeColor {a,b} = 2 * sqDist a b       (a ≠ b).
```

An edge belongs to `P.powersetCard 2`, so its two endpoints really are distinct. The factor two is harmless for equality classes and is explicitly accounted for in the Q bridge.

The later additions to `E1087.lean` were also reviewed:

- `planeEdgeLength e := sqrt(planeColor e / 2)`;
- `planeEdgeLength_pair` identifies its value on a two-point edge with `planeDistance`;
- `planeColor_nonneg` proves the required sign condition for every finite e;
- `edge_length_color_card` proves equality of the numbers of distinct lengths and distinct colors by injectivity of `t ↦ sqrt(t/2)` on the nonnegative color image;
- `planar_degenerate_iff` proves that a four-set has positive weight exactly when its six edges have fewer than six distinct ordinary Euclidean lengths.

In particular, the injectivity argument does not mistakenly assert that square root is injective on all reals. The nonnegativity hypotheses are supplied before invoking `Real.sqrt_inj`.

## The planar obstruction

In `no_four_equidistant`, set `u=b-a`, `v=c-a`, `w=d-a` in real coordinates and let `ρ=sqDist a b>0`. The five distance equalities imply

```text
u·u = v·v = w·w = ρ,
u·v = u·w = v·w = ρ/2.
```

The displayed polynomial `hGram` is the determinant of the Gram matrix of three vectors in two dimensions. Its vanishing is proved by `ring` directly from their six coordinates, rather than assumed as a geometric axiom. After the substitutions, the determinant is `ρ^3/2`. Positivity of `ρ` makes this nonzero, yielding the contradiction.

The theorem only takes `a ≠ b` as an explicit inequality. This is sufficient, not a missing distinctness assumption: the equal-distance hypotheses and that one positive distance force the contradiction. `four_set_has_different_edge_colors` independently extracts four distinct points from a four-element Finset and supplies every required edge and equality.

No noncollinearity premise is inserted. Collinear finite sets remain in the scope of all final universal results.

## Why ten is a proved bound

`monochromatic_pairs_le_ten` concerns an actual set E of six objects, with two objects known to have different colors. Let A be the color class of one selected object and B its complement in E. Both sets are nonempty, disjoint, and their sizes sum to six.

The proof maps `A × B` injectively to unordered two-element sets. The two classes cannot be swapped without violating their disjointness. Thus it constructs `|A||B|≥5` distinct cross-color pairs, all disjoint from the monochromatic pair set. There are only `choose(6,2)=15` pairs altogether, leaving at most ten monochromatic pairs.

`weight_plane_le_ten` supplies the six objects as the six actual edges of a four-point set. The required two colors are supplied by the proved planar obstruction. No “not all distances equal” or “weight at most ten” hypothesis remains in this planar theorem.

## Exact meanings of the counts

| Source notation | Implemented object | Correspondence reviewed |
| --- | --- | --- |
| Edges | `edges P = P.powersetCard 2` | Unordered pairs of distinct points, without orientation or multiplicity. |
| Equal-edge pair | `equalPairs P planeColor` | A two-element set of distinct edges, whose colors all agree. `pair_mem_equalPairs_iff` and the length bridge provide the intended meaning. |
| F | `badCount P planeColor` | Four-element subsets with positive weight. `planar_degenerate_iff` identifies this with fewer than six distinct Euclidean edge lengths. |
| W | `totalWeight P planeColor` | Sum of the actual equal-edge-pair cardinalities over all four-subsets. |
| T | `(trianglePairs P planeColor).card` | Equal-edge pairs whose union has three points; their intersection is proved to be a singleton. |
| B | `(disjointPairs P planeColor).card` | Equal-edge pairs whose union has four points; since both edges have two points, they share no endpoint. |
| Q | `(planeQuadruples P).card` | Ordered `(a,b,c,d)∈P^4` with equal, strictly positive Euclidean distances. Repetitions across the two edges are allowed. |

The source defines T literally as pairs `(a,{b,c})` with three distinct points and equal distances from the distinguished apex a. The implemented T instead stores `{{a,b},{a,c}}`. `triangle_pair_unique_apex` proves that any implemented object has a singleton intersection, so the inverse representation is mathematically well-defined: take that unique intersection as the apex and the two remaining endpoints as the unordered base. This includes collinear midpoint configurations and counts an equilateral triangle once for each apex, as required.

A separate Finset of apex/base pairs and a theorem equating its cardinality to `trianglePairs.card` have not been formalized. Therefore documentation should say that T is represented by shared-endpoint unordered equal-edge pairs, rather than claim that the code literally uses the original Cartesian-product definition. This representation boundary does not turn the proved identity into a conditional statement about an assumed T.

`planeQuadruples_eq` proves an equality of actual finite sets, converting the positive-distance condition to the two nondegenerate-edge conditions and the equality of doubled squared distances. It does not require all four coordinates to be distinct. This is the convention needed for the diagonal contribution `2n(n−1)`.

## Identities and scope

`totalWeight_as_support_sum` performs the incidence double count after proving the restriction formula for equal pairs. The numbers of four-subsets containing a three-point or four-point support are proved to be `n−3` and one. This gives `W=B+(n−3)T` from the definitions.

The orientation module proves two orientations per edge and four orientation choices per ordered pair of edges, then splits equal ordered edge pairs into diagonal and off-diagonal cases. The main file specializes this to Euclidean data and uses the support partition, yielding `Q=2n(n−1)+8(T+B)`. The reviewer authored that module, so the separate fresh replay is particularly relevant to its certification.

The combined natural-number identity is stated only for `n≥4`, where replacing `n−3` by `(n−4)+1` is valid. The unweighted/weighted comparison itself holds for every finite P, including sets too small to have any four-subset. Its upper bound is supplied by the universal geometric theorem, rather than retained as a premise.

No Guth–Katz or Katz–Tardos estimate is used to prove these finite identities. The package does not establish the original open asymptotic bound for Erdős 1087, and this review should not be read as asserting it.

## Sharpness code inspected during development

The added example uses `(0,0)`, `(2,0)`, `(3,sqrt 3)`, `(1,sqrt 3)`, matching the credited source. Its five listed short edges have squared Euclidean length four; the remaining edge has squared length twelve. Hence ten monochromatic edge pairs are available and the universal upper bound makes the weight exactly ten.

The inspected draft proves the four-point and five-short-edge cardinalities, membership of those edges, their common color eight, `sharpSet_weight = 10`, and `sharpSet_badCount = 1`. These claims match the mathematics. The final compiled status and any additional total-weight sharpness corollary are left to the completing author and fresh package replay; this review did not independently compile those changing additions.

## Review limits

- Source inspection and mathematical correspondence review only in this pass; no repeated full build or alternate kernel replay.
- No revalidation of every Mathlib dependency, cache, or toolchain artifact.
- No claim that this review is an external human review or a wholly independent authorship check.
- No substantive geometry correction was requested. The T representation boundary and the unfinished-at-review sharpness verification are disclosed above.
