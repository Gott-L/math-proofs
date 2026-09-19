# Erdős 1063: a subexponential upper bound

This package extends the fixed-rate formalization in [PR601](https://github.com/TheJustinSunPrize/awards/pull/601), pinned to commit `5130380a1d7f3ed00b827c666c79c89e202c3fdc`, to the following quantified endpoint:

For every real `ε > 0`, for all sufficiently large natural numbers `k`, there is an actual natural number `n ≥ 2k` such that exactly one of `n, n−1, …, n−k+1` fails to divide `choose(n,k)`, and

`n ≤ exp(ε k)`.

Consequently, for the least such natural number `n_k`,

`log(n_k) = o(k)` as `k → ∞`.

The mathematical subexponential conclusion is already present in the cited prior work. The contribution described here is the extension of the pinned Lean proof to this quantified endpoint, together with a Lean 4.19 adaptation and an elementary prime-count estimate. It does not assert a new mathematical discovery, worldwide formalization priority, a sharp asymptotic for `n_k`, or resolution of every interpretation of the request to estimate `n_k`. Attribution and source-access limits are recorded in [SOURCES.md](SOURCES.md).

## The exact quantity being bounded

`Admissible k n` means

```text
2*k ≤ n, and there exists i0 < k such that
  (n−i0) does not divide choose(n,k), and
  for every i < k with i ≠ i0, (n−i) divides choose(n,k).
```

All subtraction and divisibility in this predicate are over natural numbers. The lower bound on n ensures that the entries of the block are positive in the relevant range `k ≥ 2`.

`leastWitness k` is the natural-number infimum of this admissible set, following the [pinned Formal Conjectures definition](https://github.com/google-deepmind/formal-conjectures/blob/cb20d7eb22b6f9866001d53fdf1ea4bb93fb34c0/FormalConjectures/ErdosProblems/1063.lean). Nonemptiness is established by constructing a witness. In fact, `SubexpNonempty.lean` obtains one for every `k ≥ 2`, so the infimum is an admissible minimum throughout that range. The argument does not use the default value of an infimum of an empty set.

## The inherited finite construction

The arithmetic and simultaneous-approximation proofs are adapted from 56647563's Apache-2.0 PR601 formalization, with its Codex assistance and mathematical attributions retained. The construction chooses an exceptional index E, supplies enough prime-power factors at that index, and uses Kummer's carry formula to prove divisibility at every other index. A prime divisor of k certifies failure at E. A finite box argument supplies the simultaneous residues needed for the remaining primes. These properties are proved before any asymptotic estimate is applied.

The resulting finite bound, retained in `SizeBounds.lean`, is the main reusable input. For natural parameters E, y, Q, M satisfying

```text
2 ≤ k,  E < k,  0 < Q,  k ≤ Q*E,  k < (y+1)^2,
```

there is an admissible n with

`n ≤ 4 * k^[3 + 2*(y + 2*E*M + floor(k/(M+1)))] * Q^π(k)`.

Here `π(k)` is defined in this package as the cardinality of the primes in `range(k+1)`. M is free. The finite theorem imposes no fixed root degree and no prime-distribution hypothesis. The adapted files and source-comparison information are described in [compatibility-notes.md](compatibility-notes.md).

## An elementary prime-count bound

`PrimeCountBound.lean` proves, for every natural k,

`π(k) * log k ≤ 6*k`.

For `k ≥ 1`, put `q = floor(sqrt(k))`. Since `q² ≤ k < (q+1)²` and `log(q+1) ≤ q`, one has `log k ≤ 2q`. There are at most q primes at most q, so their contribution to `π(k) log k` is at most `2q² ≤ 2k`.

Every remaining prime p satisfies `k < p²`, hence `log k ≤ 2 log p`. Sum over those primes and enlarge to all primes at most k. Mathlib's elementary inequality `primorial(k) ≤ 4^k` gives a contribution at most

`2 log(primorial(k)) ≤ 2k log 4 ≤ 4k`.

Adding the two parts gives the stated constant 6; `k = 0` is immediate. This proof needs neither the prime number theorem nor a short-interval prime theorem. The constant is deliberately coarse.

## A degree chosen after ε

Fix an integer `d ≥ 4`. Define t to be the largest natural number with `t^d ≤ k`. In Lean 4.19 this is implemented with `Nat.findGreatest`; the proofs establish

`t^d ≤ k < (t+1)^d`.

For `k ≥ 2^d`, set

`E = y = floor(k/t²)+1`, `Q = t²`, and `M = t`.

Then `t ≥ 2` and `t^4 ≤ k`. The finite parameter arithmetic verifies every hypothesis of the construction and proves

`(E + 2Et + floor(k/(t+1))) * t ≤ 7k`.

Writing `A = 3 + 2*(E + 2Et + floor(k/(t+1)))`, it follows that `A*t ≤ 17k`. Thus the finite bound is `4*k^A*(t²)^π(k)`.

The logarithm of its last factor is bounded using the prime-count estimate and `d log t ≤ log k`:

`π(k) log(t²) ≤ (12/d) k`.

For each fixed d, the other terms satisfy

`log 4 + A log k ≤ log 4 + 17d*k*log(t+1)/t = o(k)`.

This uses only `log x = o(x)` and the fact that t tends to infinity for fixed d. The Lean proof obtains an arbitrary positive linear bound on these terms; it does not leave this estimate as an assumption of the final witness theorem.

Now give `ε > 0`. Choose d with `d ≥ 4` and `12/d ≤ ε/2`. After fixing that d, choose a threshold for k that makes the remaining logarithmic cost at most `(ε/2)k`. The total is at most `εk`, proving the required witness bound.

The order of quantifiers matters: ε is given first, d is then chosen, and the threshold may depend on both. No estimate uniform over all d is needed. A single fixed positive exponential rate would not prove this endpoint.

## Passing to the actual minimum

`Erdos1063.subexponential_witness` supplies an admissible n with the bound for each sufficiently large k. The natural infimum is at most this n. Its membership in the admissible set gives `leastWitness k ≥ 2k`, hence positivity and a nonnegative logarithm for `k ≥ 2`.

Taking logarithms yields, for every `ε > 0`, eventually

`0 ≤ log(leastWitness k) ≤ ε*k`.

This is the little-o statement in Mathlib's norm-based definition. The infimum bridge is proved in `SubexpInfimum.lean`; its quantified witness premise is supplied by `SubexpAsymptotic.lean` when the endpoints are assembled.

## Scope and checking

The source files distinguish the reused finite proof, compatibility wrappers, elementary prime count, parameter extension, and infimum bridge. This outline is an explanation of those arguments, not an independent external review or an official acceptance record. Compilation, axiom inspection, and full-package replay results are recorded separately when performed; no verification totals or operator decision are asserted here.

Gott-L provided project initiation, objectives, planning, and research direction. Codex assistance supplied the new implementation, adaptation, mathematical checks, and documentation. The authoring workflow for this outline also participated in the proof, including `PrimeCountBound.lean`.
