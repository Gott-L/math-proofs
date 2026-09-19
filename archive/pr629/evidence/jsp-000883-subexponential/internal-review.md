# Internal semantic review of the subexponential upper bound

This report concerns the exact Erdős 1063 minimum and the quantified subexponential upper bound. It distinguishes reused finite proofs, new formal estimates, and the separate replay recorded below. The mathematical result is credited to Patrick White and Ricky Cipollini, with their stated collaborators; this review makes no new-discovery, global first-formalization, or award-eligibility claim.

The reviewer is another Codex agent on the same team. It wrote `CarryCompatibility.lean` and ported the three reused finite-proof modules. It did **not** write the new prime-count, size adaptation, arbitrary-degree parameter, asymptotic, minimum, nonemptiness, or final submission proofs. This is internal cross-module AI review with disclosed participation, not independent human or official prize verification.

## Original problem and unchanged minimum

The minimum is the natural-number infimum of the set of n satisfying

```text
2*k <= n
and there is i0 < k with (n-i0) not dividing choose(n,k),
while every i < k different from i0 satisfies (n-i) divides choose(n,k).
```

This is the literal set in the [fixed original PR 601 Submission.lean](https://github.com/56647563/awards/blob/5130380a1d7f3ed00b827c666c79c89e202c3fdc/submissions/jsp-000883/Submission.lean), which attributes the definition to the Formal Conjectures Authors. `Admissible` abbreviates precisely this predicate. A `Fin k` restriction, a different binomial coefficient, an unproved uniqueness premise, or a modified comparison function has not been substituted.

The asymptotic endpoint is about this actual least n, not just a convenient constructed upper bound. Moreover, `admissible_exists` establishes nonemptiness for every k>=2 by applying the finite construction with E=1, y=k, Q=k. These parameters satisfy E<k, 0<Q, k<=QE and k<(y+1)^2. Consequently `leastWitness_spec` proves that the natural infimum itself is admissible for every k>=2. Its comparison with any other admissible n is also proved. Thus the convention for the infimum of an empty natural-number set cannot make the advertised endpoint vacuous.

The result is an upper bound. It does not give the exact asymptotic order of this minimum or a matching lower bound.

## Reused finite arithmetic and its compatibility bridge

The inspected finite proof is [56647563's PR 601 formalization with Codex assistance](https://github.com/56647563/awards/tree/5130380a1d7f3ed00b827c666c79c89e202c3fdc/submissions/jsp-000883), under Apache-2.0. [compatibility-notes.md](compatibility-notes.md) and [port-metadata.json](port-metadata.json) record its source hashes, exact limited interface changes, and preserved attribution. The finite construction is not presented as original work of this packet.

The compatibility carry formula follows from the existing Mathlib multiplicity version of Kummer's theorem. The second counting bridge identifies the positive prime powers dividing a positive integer with the interval up to its factorization exponent; the explicit upper cutoff follows from `p^v <= n < p^b`. Both interfaces are proved, not declared as mathematical axioms.

The finite proof's large-prime branch injects each relevant exponent into a carry at the same level. Above the window length, divisibility of a numerator factor forces the required carry. The small-prime branch bounds off-center valuations by the size of the nonzero offset, then supplies any missing carry budget with extra depth at the center. The chosen prime divisor of k has a strict carry deficit, so the designated center is actually proved not to divide the binomial coefficient. It is not simply omitted from the divisibility proof.

The simultaneous approximation step uses a finite pigeonhole argument on residue boxes. It supplies an integer multiplier between 1 and Q to the power of the regular-prime count. All relevant residue requirements are discharged in `exists_bounded_witness`. The factor 2k in the anchor establishes the required n>=2k, and hence the positivity needed for factorization and division.

## Finite size bound and prime count

The exceptional-prime count splits by the quotient k/p. When that quotient is at most M, the map p -> (k/p, k mod p) is injective because the quotient is positive and the two coordinates reconstruct k. There are at most 2EM such pairs. In the complementary part, p<=k/(M+1). This supplies the finite size bound without a prime-distribution assumption.

The resulting witness bound is

```text
n <= 4 * k^[3 + 2*(y + 2*E*M + floor(k/(M+1)))] * Q^primeCount(k).
```

The new `primeCount` is exactly the number of prime natural numbers p<=k. To bound it, the proof separates primes at q=floor(sqrt(k)). The small-prime contribution to primeCount(k)*log(k) is at most 2k. For each larger prime, k<p^2 gives log(k)<=2log(p). The sum of these nonnegative prime logarithms is at most log(primorial(k)); Mathlib's proved bound primorial(k)<=4^k and log(4)<=2 bound the large-prime contribution by 4k. The case k=0 is handled separately. Therefore the proof establishes, for every k,

```text
primeCount(k) * log(k) <= 6*k.
```

There is no invocation of the prime number theorem, a short-prime-interval conjecture, or a supplied asymptotic prime-count hypothesis.

## Arbitrary positive rate and order of quantifiers

For a fixed integer d>=4, `scale d k` is the greatest t with t^d<=k. Its definition uses a bounded natural-number search, and the code proves both t^d<=k and k<(t+1)^d. For k>=2^d, t>=2 and t^4<=k.

Set E=y=floor(k/t^2)+1, Q=t^2, and M=t. The parameter arithmetic proves every finite-construction hypothesis. If A denotes the polynomial exponent in the finite size bound, it also proves A*t<=17k. These statements are not premises remaining in the final witness theorem.

For each fixed d and every delta>0, `eventually_anchor_log_bound` proves

```text
log(4) + A*log(k) <= delta*k
```

eventually. It uses log(k)<=d*log(t+1) and log(t+1)/t -> 0. The threshold is allowed to depend on the fixed d and delta. The proof explicitly transfers a sufficiently large t threshold to a k threshold using k>=N^d; it does not assume uniformity in d.

The prime-count inequality and d*log(t)<=log(k) give

```text
primeCount(k) * log(Q) <= (12/d)*k.
```

Given any positive real epsilon, `exists_degree_small_rate` first chooses a natural d greater than both 4 and 24/epsilon. This yields 12/d<=epsilon/2. The proof then uses delta=epsilon/2 and chooses the required eventual k threshold for that fixed d. Consequently the complete witness statement has the correct order

```text
for every epsilon > 0,
there is a natural K,
for every k >= K,
there is an actual admissible n with n <= exp(epsilon*k).
```

A single fixed positive exponential rate is not being relabeled as subexponential. The real exponential comparison is obtained from logarithms of positive natural bounds, with positivity proved before using `exp(log(x))=x`.

## From witnesses to the least value

The minimum is at most each constructed witness. For k>=2 it is itself admissible, so it is at least 2k and its logarithm is nonnegative. Combining these facts with the arbitrary-epsilon upper bound verifies the norm inequality required for

```text
log(leastWitness(k)) = o(k).
```

The final limit `log(leastWitness(k))/k -> 0` follows from the proved little-o statement. The natural infimum has been expanded in the review's raw endpoint checks; those checks do not replace it with a different function or assume the existence result that the packet is meant to establish.

## Verification record

The separate replay uses a new directory containing byte-for-byte copies of the frozen local proof modules. Its import path includes that directory and the nine pinned dependency library directories, excluding pre-existing local proof output. Existing Mathlib caches are reused, not independently rebuilt; the Lean kernel and those libraries remain trusted dependencies. All compilation is requested with Lean 4.19, `-s 65536`, and warnings treated as errors.

[review-a/Audit.lean](review-a/Audit.lean) contains the review's own explicit statements: literal admissibility and minimum definitions, the exact prime-count inequality, the finite witness bound, degree-after-epsilon and threshold order, the fully written-out witness predicate, actual minimum membership and minimality, and the quantified minimum/little-o/limit endpoints. The axiom audit checks named public source declarations and these review statements. Only `propext`, `Classical.choice`, and `Quot.sound` are permitted.

The successful replay result and exact source hashes are recorded in [review-a/receipt.json](review-a/receipt.json). All eleven frozen modules, twelve explicit review statements, and the generated axiom audit compiled without warnings. All 98 requested axiom reports were present: 86 public proof definitions/theorems and twelve review statements. Every reported dependency was in the standard three-axiom allowlist. The proof-source hashes were unchanged after replay. A separate source scan found no proof placeholders, custom axiom declarations, native-decision shortcuts, or unsafe declarations in the eleven proof modules. The public receipt uses relative source names and contains no local absolute paths or private contact details.

No mathematical or statement-correspondence defect was found in the reviewed scope. This assessment concerns the frozen code and the stated upper bound; it does not certify global priority, prize eligibility, or all related manuscripts. In particular, Cipollini's full Overleaf manuscript was not obtained in this workflow; the direct reuse and source correspondence reviewed here concern the pinned PR601 files, with that prior-work reference retained and its access limit disclosed in SOURCES.md.

## Frozen source hashes

| File | SHA-256 |
| --- | --- |

| CarryCompatibility.lean | `d0af426bc14878c6421f8f2c7620f473131afe0ce17f05c7942c3f8f9cbe0d4a` |
| OneCarry.lean | `5bb8a45686bf867b65913f31d71de7bd8a44a41e0d98f2650db2e948b6bb7352` |
| FiniteConstruction.lean | `8c6b482b71bff076bd06abcae5e06c15fff09272325739951cae36eed529dca8` |
| Simultaneous.lean | `e926e2f083729b8d8f5229095d8700177527ad4df999842e985e97663384d469` |
| PrimeCountBound.lean | `7ccdb00bacb7b68514931f3f5c49f1ec20b73e2f2b211bd33a6ab3f6c71f44fc` |
| SizeBounds.lean | `fdf385fe004d3240539fa87a6fe13b26c67e601d7dc8108971503aa7155700a5` |
| SubexpParameters.lean | `7613bb3bbeb5d7372ef26214207a9a74fbc2d06d3f5d4cf91667be46e3379a81` |
| SubexpAsymptotic.lean | `25ad762837737d07d2d0cccc463e2829be0954afc06721f608f17931dea089f6` |
| SubexpInfimum.lean | `9024e1a9d14a2f7520f51d0450d76af0d2095be11cdf13802f972a30589f04bd` |
| SubexpNonempty.lean | `d0d1655a5c427acd4925b6be789b61382c1efa73f0dcb05a3c72ba387c01dd57` |
| SubexpSubmission.lean | `1141f64324c746c10e12ce12c4eed7e8d3a6d8ea1448cf801dc3e55f721a39e1` |

Review Lean code is Apache-2.0; this explanatory report is CC BY 4.0 with the original attributions retained.
