# JSP-000295 / Erdős 357: lower density zero

This packet gives a complete Lean proof of the known infinite-sequence theorem:

> A strictly increasing sequence of natural numbers whose distinct finite consecutive blocks have different sums has a range of lower natural density zero.

The exact endpoint is the registered [Formal Conjectures variant](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/357.lean):

```lean
theorem Erdos357.erdos_357.variants.infinite_set_lower_density
    (A : ℕ → ℕ) (hMono : StrictMono A) (hDistinct : Erdos357.HasDistinctSums A) :
    (Set.range A).lowerDensity = 0
```

**This proves lower density zero. It does not prove that the density limit exists, that the full density is zero, that the reciprocal series converges, or that the finite extremal function is `o(n)`. Those are different open scopes in the original problem.**

## Definitions and correspondence

`HasDistinctSums` retains the upstream generic definition: the sum map is injective on finite index sets whose coercions to sets are order-connected. The proof uses positive-length natural intervals `Ico j (j+r)` and proves that equality of their sums forces both their starting points and lengths to agree.

Mathlib 4.19 does not contain the upstream utility's `Set.lowerDensity` declaration. `E357DensityDefs.lean` therefore includes a small attributed compatibility extraction from the [same pinned density source](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/Data/Set/Density.lean). It preserves the generic order, ambient set, default `univ`, strict initial interval, real division, and liminf. For a natural-number set `S`, the resulting definition is proved equal to

$$\liminf_{b\to\infty}\frac{\#(S\cap[0,b))}{b}.$$

The verifier checks the definitions against their full formulas and separately checks the final theorem with both the distinct-sums hypothesis and the liminf conclusion expanded. No conclusion is replaced by a differently named growth property, and no unfinished theorem from the upstream problem file is imported.

## Complete proof

First suppose that a positive integer `C` bounds all terms by `A(u)≤C(u+1)`. Put `R=4C+1`, `N=2^(2R)` and `q=2^(2R-1)`, so `N=2q`. For each integer `t<R`, select all consecutive blocks with length and starting index in

$$2^t\le r<2^{t+1},\qquad 0\le j<2^{2R-t-1}.$$

There are exactly `q` blocks in each layer. Different layers have disjoint length ranges, so altogether there are `Rq` blocks. The distinct-sums hypothesis makes all their sums different. Yet every selected sum satisfies

$$\sum_{u=j}^{j+r-1}A(u)\le Cr(j+r)=C(rj+r^2)<2CN=4Cq,$$

because both `rj<N` and `r^2<N`. Thus `Rq` different natural numbers must fit in a set of size `4Cq`, contradicting `R=4C+1` and `q>0`. A uniform linear upper bound is impossible. This counting lemma does not require monotonicity; it uses the global term bound directly.

Now suppose the range of the strictly increasing sequence has positive lower density. Choose a positive number below that liminf. Eventually all initial-segment densities exceed it. There are exactly `n` range elements strictly below `A(n)`, so this eventual density inequality implies a linear bound on `A(n)` for all sufficiently large `n`. A larger positive integer constant absorbs the finite initial segment. This contradicts the counting lemma. Since lower density is nonnegative, it must equal zero.

The proof uses the liminf's eventual lower bound; it never assumes convergence of the density ratios. The initial-segment cardinality, positive denominators and finite initial segment are handled explicitly.

## Prior work and attribution

The mathematical result is recorded by Paul Erdős in *Problems and results on combinatorial number theory III* (1977), p. 70 ([original PDF](https://www.renyi.hu/~p_erdos/1977-27.pdf), [DOI](https://doi.org/10.1007/BFb0063064)). The paragraph separates this known lower-density conclusion from the conjectures about full density and reciprocal sums. This packet reconstructs an elementary dyadic proof and formalizes known mathematics; it is not a mathematical discovery claim.

Related [prize PR #377](https://github.com/TheJustinSunPrize/awards/pull/377) and [Formal Conjectures PR #4918](https://github.com/google-deepmind/formal-conjectures/pull/4918) / [#4967](https://github.com/google-deepmind/formal-conjectures/pull/4967) address finite lower constructions and their asymptotic consequences. Their complete relevant custom Lean source closures were inspected. They do not supply this universal infinite-sequence result; see [prior-review.md](prior-review.md) for the exact search boundaries. Existing assumptions named as axioms and category-label changes were not counted as proofs. No previous complete Lean proof of this exact endpoint was located in the bounded review, but that does not establish global first priority.

**Gott-L** proposed and initiated the project, set its objectives and research direction, and owns and authorizes this submission. **OpenAI Codex** performed the candidate research, proof reconstruction, Lean implementation, documentation and internal checks. Erdős retains the mathematical attribution; the Formal Conjectures authors retain attribution for the copied definitions and registered statement. No code from the related finite-construction proofs was incorporated.

## Reproduction

Lean `4.19.0` and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned, together with transitive revisions in `lake-manifest.json`. Six modules form the complete local dependency chain:

| Module | Role |
| --- | --- |
| `E357DensityDefs.lean` | Exact density definitions and natural-number correspondence |
| `E357Intervals.lean` | Exact distinct-sums definition and interval-sum facts |
| `E357DyadicBounds.lean` | Layer sizes, disjointness and common sum bound |
| `E357Counting.lean` | Finite injective-count contradiction |
| `E357DensityBridge.lean` | Positive lower density implies a global linear term bound |
| `E357.lean` | Complete registered lower-density theorem |

With the pinned dependencies fetched, obtain the required Mathlib caches and run:

```text
lake exe cache get Mathlib.Data.Real.Archimedean Mathlib.Data.Set.Card Mathlib.Order.Interval.Finset.Nat Mathlib.Order.Interval.Set.OrdConnected Mathlib.Algebra.Order.BigOperators.Group.Finset Mathlib.Data.Finset.Prod Mathlib.Order.LiminfLimsup Mathlib.Order.WellFounded Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
python verify.py
```

The verifier freshly compiles all six copied sources with warnings treated as errors, excludes old local build products, audits 20 named declarations, and checks five exact definition/endpoint types. Only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms are allowed; `sorryAx` is rejected. Pinned Mathlib caches are trusted as the dependency environment, rather than rebuilt from source.

All six modules passed fresh compilation, all 20 named declaration audits passed, and all five definition/endpoint checks passed; the source hashes and results are recorded in [verification.json](verification.json). A separate same-team review also freshly compiled the six frozen sources, audited every explicit declaration, and checked five independently transcribed definition/endpoint types, including the final statement with both its hypothesis and conclusion fully expanded. See [internal-review.md](internal-review.md), [internal-replay.json](internal-replay.json), and [ReplayTypedAudit.lean](ReplayTypedAudit.lean). The reviewer authored the density-definition compatibility layer, so that component received an author recheck. These are internal checks, not official prize verification or independent human review.

## License

Proof code and scripts use Apache-2.0; documentation uses CC BY 4.0. Upstream copyright and source attribution are retained in the compatibility modules and `NOTICE`. Dependencies retain their own licenses. The public packet contains no private contact, payment or identity-document information.
