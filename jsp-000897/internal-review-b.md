# Internal source and mathematical review — JSP897 / Erdős 1079

2026-09-20. **PASS: no blocking semantic or mathematical issue found in the reviewed version.**

This is same-team cross-review by the Codex B agent, the author of
`NeighborhoodBound.lean`. Root reviewed that component; this document does not
represent an external independent verification or independent review of my own
authored contribution. I did not rerun compilation during this review.

## Exact conclusion and reasoning

For every natural `n ≥ 2`, `r ≥ 4`, and every simple graph on `Fin n`, the
non-strict main theorem assumes exactly `ex(n,K_r) ≤ |E(G)|`. It supplies a
maximum-degree vertex `v` with `n ≤ 2*degree(v)` and at least
`ex(degree(v),K_(r-1))` edges in its actual open-neighborhood induced graph.
The strict version replaces both edge-threshold comparisons by strict ones.
There is no additional clique-free hypothesis on `G`, no bound `r ≤ n`, and no
unprovided combinatorial supplier. `DecidableRel` is the usual adjacency
decision instance on a finite type, available classically; it is not a
mathematical restriction to a special graph family.

* **Extremal semantics:** `SimpleGraph.extremalNumber` is Mathlib's finite maximum
  over graphs with no injective, not necessarily induced, copy of the forbidden
  graph. It is not redefined as a formula. The new complete-graph bridge correctly
  identifies that property with clique-freeness: an injective copy of a complete
  graph automatically reflects adjacency, by looplessness.
* **Join bound:** the added vertex class is independent, all crossing edges are
  present, and a clique uses at most one new-class vertex. A putative `r`-clique
  therefore supplies an `(r-1)`-clique in the old graph. The proof obtains an
  actual finite maximizer, counts its join by the degree-sum identity, and proves
  `ex(d,K_(r-1)) + d*(n-d) ≤ ex(n,K_r)`. Empty classes and `d=0` are covered; the
  `r≥3` condition supplies an admissible empty graph. No Turán theorem or extremal
  closed formula is assumed.
* **Degree bound:** the balanced-product lower bound follows by discarding a
  nonnegative summand of the join bound. The even/odd split proves
  `n² ≤ 4*floor(n/2)*ceil(n/2)+1`. Together with `2|E(G)| ≤ n*maxDegree`, assuming
  `n>2*maxDegree` would force `n≤1`, contradicting `n≥2`. Thus the odd-order
  rounding and the smallest permitted order are accounted for.
* **Final combination:** the neighborhood count uses `G.neighborSet v`, not a
  surrogate or a selected subset. Its complement-incidence upper bound and the
  join inequality yield the proved surplus inequality
  `ex(d,K_(r-1)) + |E(G)| ≤ L + ex(n,K_r)`. Natural-number linear arithmetic then
  gives both main thresholds. Existence of a maximum-degree vertex follows from
  `n≥2`; no positive-degree assumption is silently supplied.

The result matches the full quantified target recorded in the existing local
`next-full-c.md` JSP897/E1079 analysis, including its linear-degree conclusion.
Known earlier complete formalizations remain prior work; this review makes no
first-formalization, clean-room, official acceptance, or prize claim.

## Actual reading and execution boundary

I read all of `JoinBound.lean`, `DegreeBound.lean`, `Main.lean`, and `Audit.lean`,
and reread my complete `NeighborhoodBound.lean`. I also read Mathlib 4.19
`Extremal/Basic.lean` in full; the copy definitions and initial implementation
in `Copy.lean` through line 155 plus the `IsContained`/`Free` definitions;
`DegreeSum.lean` lines 48–99; and the relevant clique, neighborhood, induced-graph,
degree and maximum-degree definitions/lemmas. The local catalogue JSP897 entry
and the existing `next-full-c.md` target/proof discussion were consulted.
This was not a new literature, priority, or full transitive-library audit.

`Audit.lean` checks both full endpoints and requests axiom output for all 16 named
theorems across the four proof modules. Source inspection found no `sorry`,
custom axiom, `admit`, or `native_decide`. I read `logs/main01/result.json`:
exit 0, source unchanged, 9.344 seconds, warnings treated as errors. I did not
rerun Main or Audit and do not describe the new full Audit as executed on the
basis of its source alone. My earlier neighborhood compilation and its three
axiom checks were actually successful in `logs/nb01` and `logs/nbaudit02`.

## Reviewed source identities

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| JoinBound.lean | 5501 | `6eddc1bdf38a9237df5880ab0d7d88e95e898039bf352d3cbf034c80e4773075` |
| DegreeBound.lean | 2753 | `b23910886ae63b60a2e7c8ee979bec7ac7ef80ce5754a1100859d841be6f6de6` |
| Main.lean | 3314 | `10c81035619eab00f86a4a1381e945cc6b024862c8fe882ea406b759a71f8260` |
| Audit.lean | 959 | `a7ececeaac3d24edb55d2cbbe7e746de8dee072aa58259ff8db9945af1a2e953` |
| NeighborhoodBound.lean | 3375 | `061450968678033f52dd8d8b33da967a7e646e5d8fcbaf4a6a66eb0148b897ad` |
