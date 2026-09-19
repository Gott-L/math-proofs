# Internal review: Erdős 886 constant-16 and constant-9 lower families

Review date: 17 September 2026. Reviewer: a separate Codex agent within the same collaborating team. This is an internal semantic and compiler review, not independent human review, a separate proof-checker implementation, official prize verification, or a priority assessment. The reviewer prepared the environment and earlier source audit, but did not author `E886Construction.lean`, `E886Window.lean`, or `E886.lean`.

**Review conclusion: pass.** The inspected implementation establishes the complete known constant-16 infinite-family variant and an additional constant-9 instance of the same construction. It does not settle the main all-epsilon conjecture. A fresh independent replay passed all three modules, 28 named transitive axiom checks, and three independently transcribed statement checks.

## Statement correspondence

The comparison target is the [immutable upstream Erdős 886 file](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/886.lean).

The local `Erdos886.Erdos886Divisors` matches its upstream namesake: it filters `Nat.divisors n` by the conjunction of the strict lower bound n^(1/2) < d and strict upper bound d < n^(1/2) + C*n^(1/2-epsilon). Both powers have real exponents and the divisor is coerced to a real number only for the inequalities. The local grouping of the epsilon and C binders makes no semantic change.

The exported theorem `Erdos886.erdos_886.variants.rosenfeld_infinite` has the exact requested quantifier and cardinality statement: infinitely many natural n have at least four distinct divisors in that filter at epsilon=1/4, C=16. `Erdos886.rosenfeld_infinite9` uses the same definition with C=9. Neither endpoint contains a hidden assumption of infinitude, an external reconstruction hypothesis, or a conditional predicate that replaces the desired divisor count.

`selected_mem_divisors` explicitly proves N(a) is nonzero before using `Nat.mem_divisors`; it does not exploit the special zero-divisor-set convention. Every constructed N is positive. The square root is converted with `Real.sqrt_eq_rpow`, and the exponent identity 1/2-1/4=1/4 is explicit. No floor, ceiling, closed interval, or integer-valued square-root substitution changes the target.

## Mathematical checks

The arithmetic module uses the known Erdős–Rosenfeld product N(a)=a(a+1)...(a+7) and four four-factor divisors. Each complementary-factor product equals N(a), yielding divisibility. The three adjacent differences are positive for all natural a, so A0<A1<A2<A3. Its cross-factor identity is B0+8(a+3)(a+5)=A3. These formulas agree with the prior construction; they are not claimed as a new family.

In `sqrt_bracket`, a>=1 gives B0>0 and B0<A0 with A0*B0=N. The two comparisons B0²<N<A0² imply B0<sqrt(N)<A0. The hypotheses required by the real square-root lemmas are supplied. This puts all four selected divisors above the strict lower endpoint without requiring four separate square-root proofs.

`fourth_root_lower` applies the nonnegative fourth-power/rpow-inverse equivalence to a². The arithmetic inequality a^8<=N implies (a²)^4<=N, hence a²<=N^(1/4), including a=0. Only positive parameters are used later.

`A3_lt_upper_of_gap` multiplies that root bound by a nonnegative C, combines it with the polynomial gap estimate, and uses the **strict** B0<sqrt(N) inequality. Thus the upper endpoint remains strict even though the polynomial estimate is non-strict. The two sufficient cutoffs are correct:

- For a=10+t with t>=0, 16a²-8(a+3)(a+5)=8t²+96t+40>0.
- For a=66+t with t>=0, 9a²-8(a+3)(a+5)=t²+68t+12>0.

The finite set S={A0,A1,A2,A3} is explicitly proved to have cardinality four. All six pairwise inequalities needed by simplification follow from the three strict adjacent inequalities. Each of its four members is then proved to lie in the exact divisor filter; `Finset.card_le_card` gives a genuine four-distinct-divisor lower bound, not four repeated list entries or four arbitrary factors outside the interval.

For any threshold M, the infinitude proof chooses a=max(10,M+1), or max(66,M+1). The arithmetic module proves N(a)>=a, so the constructed integer N(a)>M. This supplies unbounded **values of N**, not merely infinitely many parameter labels. `Set.infinite_of_forall_exists_gt` therefore proves the required infinite sets.

## Scope, attribution, and limitations

The local comments correctly credit Erdős–Rosenfeld for the mathematics and Jarek Koch for the prior constant-64 formalization. The arithmetic adaptation retains Koch's MIT copyright and permission notice; the statement module acknowledges the Apache-2.0 upstream definition. This review is a scope and provenance check, not a legal opinion.

The remaining main question asks for an eventual bound for every positive epsilon, independent of n. Two explicit lower-family constants do not address that open quantifier pattern. Constant 9 is a narrower sufficient interval for the same old family; it is not asserted to be the best possible constant, a new mathematical result, or a first formalization. No theorem here counts all divisors exactly, proves that there are only four, or establishes prize eligibility.

The source scan found no `sorry`, `admit`, custom `axiom`, `native_decide`, `unsafe`, `implemented_by`, or `extern` token in the three submitted Lean sources. This scan supplements the compiler and transitive axiom checks; it is not a substitute for them. Cached Mathlib dependencies are accepted at the pinned revision, rather than rebuilt from scratch.

## Final-source replay

After the authors froze the sources, the reviewer copied all three modules to a fresh temporary directory under `review886-a/`. The search path excluded the existing project's local compiled-proof directory. The modules were compiled in dependency order with Lean 4.19.0, `-s 65536`, and `-DwarningAsError=true`, using the pinned Mathlib cache at commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. All three passed without warnings. Source bytes were checked again after compilation to ensure the review did not straddle a source change.

| Frozen module | SHA-256 |
| --- | --- |
| `E886Construction.lean` | `f854f19e88594d41f7571ef5757c733b89bef44ccbcc621ec11651b65bf2c4ac` |
| `E886Window.lean` | `e3633e9a66c7ac0546294402b6d1907f1c2c8994e778396095a2049ab6fff843` |
| `E886.lean` | `5dc703c45f115d145615e0252830f0b24c003c6ff53a7cfa0bd3fd370575b19f` |

The final `fourth_root_lower` proof explicitly uses `Real.rpow_natCast` to change the real exponent 4 to the natural exponent 4, followed by a ring identity. This resolved the author's earlier elaboration issue without changing the mathematical statement.

The reviewer additionally compiled:

1. A definitional equality between the complete local divisor-filter definition and an independently transcribed filter with explicit natural divisor binders, for every n, epsilon, and C.
2. A C=16 infinitude statement with the entire divisor filter expanded, the two strict real inequalities explicit, and the fourth-root exponent directly written as 1/4.
3. The same fully expanded statement at C=9.

All three checks passed. The first attempt at the review-only transcription omitted the explicit natural type on the divisor lambda binder, causing Lean to infer a real type. Adding `(d : ℕ)` fixed the review harness; no submitted proof source was changed.

All 28 named theorem audits passed. The two final endpoints depend on exactly `propext`, `Classical.choice`, and `Quot.sound`; the earlier arithmetic lemmas use subsets of that same allowlist. There is no `sorryAx` or other unapproved dependency. The original internal review harness is retained locally. Its machine-readable result, source hashes, compiler outputs, and all named axiom lists are published in [independent-replay.json](independent-replay.json). The public packet supplies portable fresh compilation and endpoint checks through `verify.py`.

This re-elaborates the local sources and checks their Lean proof terms using the same Lean kernel implementation as the authors. It does not rebuild Mathlib, use a separate kernel implementation, certify original mathematics, or constitute organizer-authorized verification.
