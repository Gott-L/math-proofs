# Internal cross-module review: Erdős 357 lower-density variant

Review date: 17 September 2026.

**Conclusion: pass.** The six modules prove the complete registered infinite-sequence **lower-density-zero** variant, with the intended distinct-consecutive-sums hypothesis and the original real-liminf definition. Fresh compilation passed for every module, all 20 explicit declarations passed transitive axiom audits, and five separately transcribed statement checks passed. No mathematical or statement-correspondence defect was found in this review.

This is an internal review by another Codex agent in the same team. The reviewer authored the `E357DensityDefs.lean` compatibility layer, prepared its environment, and participated in earlier planning. Accordingly, the review of that module is an author recheck; the remaining modules received cross-module review. This is not independent human review, a separate kernel implementation, organizer-authorized verification, or a priority certification.

## Exact statement and definitions

The comparison target is `Erdos357.erdos_357.variants.infinite_set_lower_density` in the [fixed Formal Conjectures source](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/357.lean#L92). It assumes a strictly increasing A : Nat → Nat whose distinct finite consecutive index blocks have different sums, and concludes that its range has lower density zero.

`HasDistinctSums` retains the upstream generic definition: injectivity of the finite-set sum on all finite index sets whose coercions to sets are order-connected. The audit additionally checked equivalence to the explicit statement that for **every** pair of finite sets J,K, if both are order-connected and their sums agree, then J=K. The domain was not restricted to equal lengths, disjoint blocks, selected dyadic blocks, or any bounded family. Empty blocks remain in the upstream domain; only the later counting argument restricts its chosen blocks to positive lengths.

The density definitions match the [fixed upstream utility](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjecturesForMathlib/Data/Set/Density.lean#L36): the numerator counts `(S ∩ B) ∩ Iio b`, the denominator counts `B ∩ Iio b`, both cardinalities are cast to real numbers before division, B defaults to the universal set, and lower density is the liminf at infinity. The local compatibility proof identifies the natural universal-ambient denominator with b. Neither a full limit nor a density-existence predicate was substituted.

The independently written typed audit passed the final conclusion with `HasDistinctSums` fully expanded into the universal finite-set implication and with the conclusion written directly as

`atTop.liminf (fun b : Nat => ((range A ∩ Iio b).ncard : Real) / b) = 0`.

A separate check used the raw original ambient-set quotient, before simplifying the universal intersections or denominator. The exact named registered theorem type also compiled. These checks tie the endpoint to the intended proposition rather than merely trusting the local helper names.

## Intervals and injectivity

`blockSum A j r` sums exactly the terms indexed by the half-open interval `[j,j+r)`. Such finite intervals are order-connected, so equality of block sums invokes the actual `HasDistinctSums` hypothesis and gives equality of the two finite intervals.

For r,s>0, each starting point belongs to its own interval. Equality of the intervals then gives both j<=k and k<=j, hence j=k. Taking finite cardinalities yields r=s because the cardinality of `[j,j+r)` is r. The positive-length hypotheses are supplied later for every selected dyadic block; no empty interval is incorrectly used to recover a start point.

Under the proposed uniform bound A(u)<=C(u+1), every index u in `[j,j+r)` satisfies u+1<=j+r. Termwise comparison and the exact interval cardinality give

`blockSum A j r <= C*r*(j+r)`.

This estimate genuinely needs no monotonicity, and the resulting stronger combinatorial lemma does not weaken the final theorem's hypothesis.

## Dyadic union and counting contradiction

The layer `dyadicBlock R t` consists of pairs **(r,j)** with

`2^t <= r < 2^(t+1)` and `0 <= j < 2^(2*R-t-1)`.

For t<R, the length interval has cardinality 2^t, and the start interval has cardinality 2^(2R-t-1). The equality of their product with q=2^(2R-1) is proved with the needed inequality t<R, so no truncated-natural-subtraction identity is assumed outside its valid range. Each r is positive because r>=2^t>0.

Layers with distinct t,u are disjoint. Their length intervals cannot overlap: if t<u, then 2^(t+1)<=2^u, whereas any shared r would be simultaneously below the first number and at least the second. Thus `Finset.card_biUnion` legitimately sums the layer cardinalities. The union I over t<R has cardinality R*q, not merely a sum that could double-count elements.

The map on I is `(r,j) ↦ blockSum A j r`. Its injectivity is global across the entire union. The interval lemma returns equality of starts and then lengths; `Prod.ext hxy.2 hxy.1` correctly switches those equalities back to the stored pair order. Consequently the image cardinality equals I.card.

Every selected block sum is below the common strict bound 2*C*2^(2R). Indeed r*j<2^(2R) follows from the two separate upper bounds; r*r<2^(2R) follows from r<2^(t+1) and t+1<=R. Therefore

`blockSum <= C*(r*j+r*r) < 2*C*2^(2R)`.

The positivity C>0 is used when preserving strictness under multiplication. Thus the entire injective image lies in the finite natural range of precisely 2*C*2^(2R) elements. Choosing R=4C+1 and q=2^(2R-1)>0 gives

`R*q <= 2*C*2^(2R) = 4*C*q`,

contradicting `(4C+1)*q>4C*q`. The finite range includes zero, so the proof does not silently subtract a possible zero sum or assume an extra positivity hypothesis on A. The conclusion is exactly that no positive natural C can satisfy the uniform linear bound for all indices.

## Positive liminf implies the forbidden linear bound

For a strictly increasing natural sequence, the proof establishes the exact set identity

`range(A) ∩ Iio(A(n)) = A '' Iio(n)`.

Strict monotonicity identifies the preimage inequality A(m)<A(n) with m<n and also ensures injectivity. Therefore the number of range elements strictly below A(n) is exactly n, including the zero-based indexing convention.

Suppose the lower density is positive and let delta be half of it. The sequence of partial densities is bounded below by zero. `Filter.eventually_lt_of_lt_liminf` therefore supplies an eventual strict lower bound by delta. The proof does **not** assume that partial densities converge, that upper and lower densities agree, or that a density exists.

Strict monotonicity gives n<=A(n). After choosing an index cutoff M=M0+1, any n>=M satisfies A(n)>=M0 and A(n)>0. Evaluating the eventual density bound at the argument A(n) and using the exact count gives

`delta < n/A(n)`, hence `A(n) <= n/delta`.

The real division steps explicitly prove the denominators A(n) and delta are positive. Choosing a natural D>=1/delta converts this into A(n)<=D*n. The proof then chooses C=D+A(M)+1. Monotonicity bounds every earlier term by A(M), so this same positive C covers both the finite initial segment and all later indices as `A(n)<=C*(n+1)`. No finite-prefix exception is left in the hypothesis sent to `no_linear_bound`.

The main theorem combines the impossibility of positive lower density with the separately proved nonnegativity of the original real liminf. This establishes equality with zero, not just a growth obstruction or a conditional intermediate lemma.

## Fresh compilation and complete declaration audits

The reviewer copied the frozen source bytes into a fresh temporary directory under `review357-a/`. The old project-local compiled-module directory was removed from `LEAN_PATH`, and the modules were compiled in dependency order using Lean 4.19.0 with `-s 65536` and `-DwarningAsError=true`. Pinned Mathlib dependencies at `c44e0c8ee63ca166450922a373c7409c5d26b00b` were reused. Source bytes were compared again after the run; no file changed during review.

| Module | SHA-256 |
| --- | --- |
| `E357DensityDefs.lean` | `606c9229d92e09087523ed6b1fb1a9f5c332afd1dd59390b54f113b4734c61da` |
| `E357Intervals.lean` | `c8220e90ccfa8f1d51b93f921f226a686501950ec47a4dacbae5ae422c557d00` |
| `E357DyadicBounds.lean` | `e9455ba7fa42b119acd39f50f29c8af3375c54ced069eafcaeefc3e89c464f7f` |
| `E357Counting.lean` | `94b1f4660670a65f4e209080b53cf3f8f126db0fa5d2267a061ac38dc9741879` |
| `E357DensityBridge.lean` | `b392346a5fc0a014bf4682cac59da641ffd4468b2e599650f8213ea46c904061` |
| `E357.lean` | `a68d29b3f4b7ebf089bbc3abc989a68eb25c0523db3a546e5c25155b983045ec` |

All six modules and the typed audit compiled successfully with warnings treated as errors. The audit list was checked against all explicit source `def`, `abbrev`, and `theorem` declarations: five definitions and fifteen theorems, twenty in total. Each transitive dependency set is contained in `{propext, Classical.choice, Quot.sound}`. The final endpoint uses exactly those three standard axioms; no `sorryAx` or extra axiom occurs. The source scan also found no `sorry`, `admit`, `native_decide`, `unsafe`, `implemented_by`, or `extern` token.

The five typed checks cover the generic expanded distinct-sums predicate, the generic raw-liminf definition, the exact registered theorem, the fully expanded endpoint with its original ambient-set quotient, and the fully expanded endpoint with denominator b. They are retained in [ReplayTypedAudit.lean](ReplayTypedAudit.lean), SHA-256 `f960f4232a899592549c1863b5fc04368fd4378c435867abeb89f187e6a3d4b5`.

The local replay harness invoked the existing project's `lake env`. Its machine-readable result is published as [internal-replay.json](internal-replay.json); the original absolute build-directory path is replaced with a relative label. The original private receipt has SHA-256 `d6e6f014af9bfca3d079d55a1ab19f32a80f221a87df4f69f4d4344adada5d09`. It records compiler outputs, source fingerprints, all named axiom lists, and the statement checks. This replay checks the local proof sources with the same Lean kernel implementation; it does not rebuild Mathlib or supply a second checker.

## Scope and provenance

Mathematical credit remains with the known observation recorded by Paul Erdős in 1977; the exact registered scope and its distinction from the remaining questions are described in the source audit. Upstream definitions retain their Formal Conjectures attribution and Apache-2.0 notices.

This implementation proves the lower-density-zero variant for an infinite strictly increasing sequence. It does not prove full asymptotic density zero, convergence of the reciprocal series, the finite extremal question f(n)=o(n), or the stronger quantitative growth assertion mentioned in the historical discussion. Successful formalization does not establish first-formalization priority, organizer acceptance, or prize entitlement.
