# Mathematical review: the Erdős–Graham exact-order criterion

17 September 2026. **No mathematical gap or weakening of the stated criterion was found in the five reviewed proof modules.** In particular, the final theorem derives its finite adjacent-length certificate from the universal divisibility hypothesis; it does not assume that certificate or the existence of an exact order.

This is an internal, non-author source review of the E336 modules. The reviewer did not implement any of these five modules, but is a Codex collaborator on the same project and contributed to other packets and the checker pilot. It is not independent external human review. No proof source was edited and no full build was repeated for this review. Compilation and transitive axiom results belong to the separate primary and replay receipts.

## Mathematical statement and source correspondence

Erdős and Graham's *On bases with an exact order*, Acta Arithmetica 37 (1980), 201–207, Theorem 1, characterizes the asymptotic bases that admit an exact order by gcd one of their consecutive differences. The definitions allow nonnegative generators and repeated summands; both orders are least successful eventual representation counts. The original paper is available through the [author archive](https://www.renyi.hu/~p_erdos/1980-22.pdf). The same definitions and characterization are explicitly recalled in the introduction of [Yang–Chen, *On bases with a T-order*, Integers 11 (2011), A5](https://math.colgate.edu/~integers/l5/l5.pdf).

The original theorem/proof was read in the project's preceding source audit, `next-unfinished-after-eight.md`. In this review, attempts to reopen the original PDF timed out or were forbidden; the accessible 2011 primary paper was read directly. Thus this review does not claim a second successful full-PDF reading of the 1980 paper.

The Lean definitions express the relevant notions directly:

| Definition | Mathematical meaning |
| --- | --- |
| `RepresentsExactly A h n` | A list of length `h`, all entries in `A`, with sum `n`; repetitions are permitted. |
| `EventuallyAtMost A r` | One threshold works for all subsequent `n`; each may use its own count `h ≤ r`. |
| `EventuallyExactly A h` | One fixed count `h` works for all sufficiently large `n`. |
| `HasExactOrder A h` | That fixed count works and every smaller count fails eventually to cover all large numbers. |
| `DifferenceGcdOne A` | Every natural number dividing all pairwise unsigned differences must equal one. |
| `ConsecutiveGcdOne a` | Every natural number dividing all `a(i+1)-a(i)` must equal one. |

The gcd condition is its universal common-divisor characterization, not an assumed finite Bézout representation. It quantifies over **every** `d : ℕ`, including zero. For all-zero differences, zero is itself a common divisor, so the condition correctly fails. The usual gcd-one meaning is preserved.

`erdos_graham_set_criterion` keeps the essential bounded-basis hypothesis `EventuallyAtMost A r` and concludes

```text
(∃ h, HasExactOrder A h) ↔ DifferenceGcdOne A.
```

It need not assume that the supplied bound `r` is the least weak order: any finite eventual bound is enough for the existence criterion. `erdos_graham_sequence_criterion` gives the consecutive-difference statement for the actual range of a strictly increasing natural sequence. It does not substitute that range for an unrelated larger set.

## The least-positive-difference argument

`BalancedDifference A z` in `E336Differences.lean:16` supplies two actual finite lists from `A` of the same length, with their sums differing by `z` in **the integers**. Using integer subtraction here avoids truncated natural subtraction. The zero, addition, negation, subtraction and natural-multiple lemmas follow by empty lists, concatenation, swapping the lists and induction. A pairwise natural distance is represented by suitably orienting two singleton lists.

The proof does not assume that a positive balanced difference exists. If every pairwise distance were zero, then `d = 0` would divide all of them, contradicting `DifferenceGcdOne A`. This gives a positive balanced difference. The same universal hypothesis also proves that `A` is nonempty.

`balancedDifference_one` (`E336Differences.lean:105`) chooses the least positive natural `d` that is a balanced difference. For any `x,y ∈ A`, put `v = Nat.dist x y`. Both `v` and `d` are balanced differences. Closure under subtraction and natural multiples gives

\[
v-\lfloor v/d\rfloor d=v\bmod d
\]

as another balanced difference. The equality is established after casting the natural division identity to the integers. Because `d > 0`, the remainder is smaller than `d`; if positive, it contradicts the actual `Nat.find` minimality property. Hence the remainder is zero and `d` divides every pairwise distance. The original universal hypothesis then forces `d = 1`.

This is a complete finite extraction argument. It neither assumes a subgroup generator nor hides a finite gcd, Bézout identity or finite-certificate theorem as an extra premise.

`adjacentLengths_of_differenceGcdOne` (`E336Differences.lean:126`) next chooses any `a ∈ A` and multiplies the balanced difference one by `a`. The resulting equal-length lists satisfy

\[
\operatorname{sum}(xs)=\operatorname{sum}(ys)+a.
\]

Appending the singleton `[a]` to `ys` gives two lists with the same sum and lengths `L` and `L+1`. Both lists and all membership proofs are explicitly constructed. If `a = 0`, the construction may give `L = 0` and common sum zero; that is valid and is handled by the subsequent padding argument.

## Padding, necessity, and least order

Suppose the adjacent lists have lengths `L,L+1` and common sum `M`. `E336Padding.lean` proves that `r` copies of this value admit every length `rL+j` for `0 ≤ j ≤ r`. For `n ≥ N+rM`, the bounded-basis hypothesis supplies a representation of `n-rM` using some `j ≤ r` summands. Choose padding length `rL+(r-j)`. Concatenation has sum `n` and fixed length

\[
j+rL+(r-j)=r(L+1).
\]

The hypotheses guarantee that natural subtraction does not truncate either required equality. `L`, `M`, `r(L+1)` and the threshold are fixed before the quantifier over `n`; the result is genuine fixed-length eventual coverage, not a length chosen separately for every number.

For necessity, `E336Necessity.lean` proves that equal-length lists from a single congruence class have congruent sums. Exact representations of `N` and `N+1` then imply `d ∣ 1`, hence `d = 1`. This reasoning works for `d = 0` as well; no silent positivity restriction is added to the universal condition.

The sequence bridge proves equality of the sets of common divisors of pairwise distances and consecutive differences. `StrictMono a` ensures the consecutive natural differences are genuine nonnegative differences; transitivity of congruence supplies the finite telescoping step between arbitrary indices.

Finally, `E336Criterion.lean` invokes the proved certificate and padding theorem. Its `Nat.find` proof of least exact order is used **after** an eventual exact count has been established. No exact-order witness is assumed on the sufficiency side.

## Edge cases and explicit scope checks

- The ambient type is `ℕ`, so zero is permitted. No lemma requires all generators to be positive.
- Lists allow repeated summands. A finset of summands would change the theorem and is not used.
- Empty lists represent zero. They cannot provide eventual exact order zero: `eventuallyExactly_pos` derives a contradiction from a representation of `N+1` with length zero.
- Empty or finite sets and a bound `r = 0` cannot satisfy the bounded-basis premise. The theorem does not silently add infinitude or a positive weak-order premise to handle them.
- Gcd one alone is insufficient for eventual bounded representation, for example for the finite set `{2,3}`. The final iff correctly retains the bounded-basis hypothesis. The finite adjacent-list result, which can hold for such a set, is only an intermediate theorem.
- All three public criterion theorems are unconditional relative to their displayed basis/range hypotheses. `AdjacentLengths` appears only as an intermediate constructed fact.

The independently transcribed statement source `TypedAudit.lean` exposes the list quantifiers, both sides of the iff, the least-order predicate, the range/consecutive version, unconditional finite extraction, repeated summands and zero-length boundary. Those are appropriate semantic checks. This review did not rerun their compiler check; the recorded primary receipt reports the result separately.

## Prior work and limitations

The mathematics remains credited to Erdős–Graham (1980). The least-balanced-difference implementation is an elementary proof organization of that known criterion, not a mathematical discovery claim. Gott-L supplied project direction; Codex implemented the formal development.

The bounded preceding source audit distinguishes this endpoint from [PR660](https://github.com/TheJustinSunPrize/awards/pull/660), pinned to `CollinYuanjieRen/awards@72be7ec71c44c6ede324331a428c9ea2bf6ba21b`, which proves an explicit weak-order-two/exact-order-three example. It also acknowledges the substantial [`plby/lean-proofs` E336 development at `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos336). Its announced extremal-limit endpoint was not rebuilt or certified by this review. The absence of this criterion in the sources previously inspected is not a global first-formalization certificate.

This package proves the complete exact-order **characterization**. It does not prove an optimal quantitative order bound or the E336 extremal-limit statement. The inspected official catalogue marks JSP-000279 **Eligible to claim: No**; neither source review nor compilation establishes an award entitlement. The earlier Nanoda pilot checked JSP-000399, not these E336 modules.

Reviewed source SHA-256 values:

| File | SHA-256 |
| --- | --- |
| `E336Defs.lean` | `c87cac6df2382f05cfe1ccb1e96e19b6bd2be76704750bc308a1b495ea738597` |
| `E336Differences.lean` | `fbe5eb0a115d6e4eefac53b4329f5b452373ea77d2314cc48763857ecec3eecc` |
| `E336Padding.lean` | `8f7161ea8319d37bd7f7e6b04299b6504e8c90e3e67da7867df71dcfcc7020f9` |
| `E336Necessity.lean` | `6ad1ca0a2e279655393df57dd043ef043d394172cdf9f474400013d758b718c6` |
| `E336Criterion.lean` | `e19ab354601835ad963100789bb104550cae25b376b7ad66b49724cace564e00` |

Original review prose is licensed CC BY 4.0. Proof and external-source licenses remain unchanged.
