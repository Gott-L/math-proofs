# Prior-source review: JSP-000904 / Erdos 1087

Research checked 17 September 2026. This records the candidate screening before implementation; completed proof and verification results are reported in README.md and verification.json. This is a bounded public-source review, not a global priority certificate.

## 1. Recommended: JSP-000904 / Erdős 1087

### Precise source and present gap

- [Official PR 586](https://github.com/TheJustinSunPrize/awards/pull/586).
- Fixed source commit: `haipapa123/awards@daa68321eca18b869069e5cdec51ab5526d57558`.
- [Complete written proof](https://github.com/haipapa123/awards/blob/daa68321eca18b869069e5cdec51ab5526d57558/docs/submissions/jsp-000904-distance-counting/PROOF.md).
- [Statement map](https://github.com/haipapa123/awards/blob/daa68321eca18b869069e5cdec51ab5526d57558/docs/submissions/jsp-000904-distance-counting/STATEMENT_MAP.md).

All five changed files were read: the proof, README, references, statement map, and exact Python checker. The 241-line written proof supplies double-counting arguments; the checker tests finitely many configurations. Neither is a Lean proof. The asymptotic estimates are credited to external theorems, and the submission correctly leaves the original general `n^(3+o(1))` problem open.

### Exact proposed endpoint

For an arbitrary finite set P of n≥4 distinct points of the Euclidean plane, define these **actual finite objects**, not variables satisfying assumed identities:

- An edge is an unordered two-element subset of P.
- `w(S)` is the number of unordered pairs of distinct equal-length edges in a four-element set S.
- `F(P)` counts four-element subsets S with `w(S)>0`.
- `W(P)` is the sum of `w(S)` over all four-element subsets.
- `T(P)` counts a distinguished apex a and an unordered base pair {b,c}, all distinct, with `dist(a,b)=dist(a,c)`. Collinear midpoint configurations are included.
- `B(P)` counts unordered pairs of equal-length edges whose endpoints are all distinct.
- `Q(P)` counts ordered quadruples (a,b,c,d) from P with equal positive distances `dist(a,b)=dist(c,d)>0`; endpoints may repeat across the two edges.

Prove, universally in P,

```
Q(P) = 2*n*(n-1) + 8*(T(P)+B(P))
W(P) = B(P) + (n-3)*T(P)
8*W(P) + 2*n*(n-1) = Q(P) + 8*(n-4)*T(P)
F(P) <= W(P) <= 10*F(P)
```

The subtraction-free combined form avoids rational division and natural subtraction ambiguities. Also prove that the constant 10 is attained by an explicit planar four-set. These are fully quantified finite-combinatorial results, not a check of selected point configurations. The identities themselves work in any metric space; the constant 10 uses the dimension-two geometry.

### Independent mathematical verification

The first identity partitions equal-distance ordered quadruples according to their two underlying unordered edges. A repeated edge contributes four orientations, giving `4*choose(n,2)=2n(n−1)`. Each unordered pair of different equal edges contributes eight quadruples (two orders and two orientations per edge). Distinct edges either share exactly one endpoint, counted by T, or are disjoint, counted by B.

For the second identity, double-count a four-set together with one equal-edge pair inside it. A disjoint pair already uses four vertices and has one containing four-set. A pair sharing its apex uses three vertices and has exactly n−3 containing four-sets. Substituting gives the combined equation.

For the comparison, every bad four-set contributes at least one. Its six edge lengths cannot all coincide: four pairwise equidistant distinct planar points do not exist. Partition six edges into their nonempty equal-length classes of sizes m_i. There are at least two classes and `w=Σ choose(m_i,2)≤choose(5,2)=10`. An elementary alternative is to choose one class of size k, with 1≤k≤5. At least k(6−k)≥5 of the fifteen pairs cross that class and its complement, so at most ten edge pairs have equal lengths.

Sharpness is witnessed by

```
(0,0), (2,0), (3,sqrt(3)), (1,sqrt(3)).
```

Five of their six squared distances are 4, and the sixth is 12. Thus F=1 and W=10. Distinctness and each distance identity must be proved, not inferred from a drawing or a floating-point computation.

### Feasible Mathlib 4.19 implementation

Recommended architecture:

1. Define edges with `Finset.powersetCard 2`, four-sets with `powersetCard 4`, and filtered equal-edge pair sets. Prove the actual support-cardinality split into three versus four endpoints. Use `Finset.sum_comm`, `card_bij`, `sum_bij`, product cardinalities, and subset-extension bijections.
2. Prove Q's orientation fibers with explicit maps/inverses; the factors 4 and 8 must come from bijections, not unchecked enumeration depending on n.
3. Prove the generic six-label combinatorial bound once two labels differ.
4. Supply the planar obstruction. One route avoids advanced geometry: translate one point to the origin and take its three difference vectors u,v,w in ℝ². The determinant of their Gram matrix is zero by a polynomial identity in six coordinates. If all six mutual squared distances equal ρ>0, diagonal Gram entries equal ρ and off-diagonal entries equal ρ/2, so the determinant is ρ³/2>0. This contradiction is entirely ring arithmetic plus positivity. The key determinant identity can be written explicitly, so no unverified rank oracle is needed.
5. Check the sharpness four-set with exact `Real.sq_sqrt` facts and ordinary kernel-proved arithmetic.
6. If an upstream statement bridge is included, explicitly prove that fewer than six distinct positive distances is equivalent to a repeated edge length on a four-set.

Expected difficulty: medium. The main cost is finset bijection bookkeeping and aligning unordered edge representations. The geometric obstruction is a small independent polynomial lemma. `PiL2`, powerset/cardinality, finite sums, real square root, and polynomial tactics are present in the local 4.19 source tree; not every needed compiled module is currently cached. Targeted dependency fetching may be needed later, but no new toolchain or large download was performed here. No code has yet been compiled for this candidate.

Do not include unconditional Guth–Katz or Katz–Tardos asymptotics unless those dependencies themselves are proved or imported from a verified source. The exact counting endpoint has independent value and does not require them. A theorem merely taking the two counting identities as hypotheses would miss the proposed contribution.

### Public Lean screening and actual source inspection

- Official exact-ID search returned PR 586 only. Its actual changed files contain no Lean source.
- [GDM PR 5859](https://github.com/google-deepmind/formal-conjectures/pull/5859) was inspected through its complete 93-line patch. It defines `IsDegenerateFourSet`, `degenerateFourSetCount`, and `f`; the open theorem and both known asymptotic bounds remain `sorry`. Its proved tests concern fewer than four points only. A successful statement-file build is not a proof of those research declarations.
- [rjwalters actual Erdos1087Problem.lean](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos1087Problem.lean) was read completely. The two purported substantive bounds are custom `axiom` declarations. Its extremal quantity is `opaque maxDegenerateQuadruples ... := 0`, rather than a proved maximum construction. There are further `sorry` declarations. It does not contain the exact weighted identity and cannot be treated as a complete proof source.
- [daedalus Erdos1087.lean](https://github.com/daedalus/alphaproof-nexus/blob/4e65a6ca81655f090a3c8dcf9f56e4a38c984f4c/problems/erdos/1087/Erdos1087.lean) was read completely; its namespace contains no theorem.
- Searches for `Erdos1087` in `plby/lean-proofs`, and code searches combining distance-quadruple/isosceles/cardinality/weighted-count terminology, found no matching completed theorem. Generic search noise and empty results are only bounded search evidence, not proof of absence.

### Attribution and licensing

The fixed source's [LICENSE](https://github.com/haipapa123/awards/blob/daa68321eca18b869069e5cdec51ab5526d57558/LICENSE) states that first-party scripts use MIT, while documentation is governed by [LICENSE-CONTENT](https://github.com/haipapa123/awards/blob/daa68321eca18b869069e5cdec51ab5526d57558/LICENSE-CONTENT), CC BY 4.0. Both were read.

For a new implementation, credit the PR 586 reduction, submitting account haipapa123, The Justin Sun Prize contributors, and the fixed revision; link its proof and the CC BY 4.0 license, and state that the Lean development is a new formalization/adaptation. Preserve attribution to Guth–Katz and Katz–Tardos only for their actual estimates if discussed. Do not imply that the new formalizer discovered the reduction or that the original author endorses the submission. Any verbatim upstream formal-conjectures declarations retain their Apache-2.0 attribution. The intended work is an independently written Lean proof, not copying an unlicensed proof artifact.

