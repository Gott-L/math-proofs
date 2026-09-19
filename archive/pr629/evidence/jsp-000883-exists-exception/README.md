# JSP-000883 / Erdős 1063: the universal exception lemma

This packet formalizes the known Erdős–Selfridge observation that at least one number in a descending block fails to divide the corresponding binomial coefficient. It addresses the `exists_exception` variant of Erdős problem 1063. **It does not prove the open asymptotic bound in the main catalogue question.**

## Formal statement and scope

The stronger local statement is

```lean
theorem Erdos1063.exists_exception_of_le {n k : ℕ}
    (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∃ i < k, ¬ (n - i) ∣ n.choose k
```

The compatibility theorem `Erdos1063.erdos_1063.variants.exists_exception` has precisely the proposition in the [pinned Formal Conjectures source](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1063.lean), with the original hypothesis `2 * k ≤ n`. The packet imports Mathlib and its own proof modules; it does not import the upstream theorem with its unfinished proof.

All quantified variables are natural numbers. The lower bound on `n` makes every block entry positive. The conclusion asserts existence of a nondivisor; it does not assert that exactly one entry is a nondivisor, nor does it estimate the least starting point for which exactly one fails.

## Proof

Choose a prime `p` dividing `k`. For a positive integer `a`, write `v(a)` for its exponent of `p`. Choose an offset `i < k` that maximizes `v(n-i)` and let `M = v(n-i)`.

For each other offset `j`, both `n-i` and `n-j` are divisible by `p^v(n-j)`. Their nonzero difference has absolute value `|i-j|`, so `v(n-j) ≤ v(|i-j|)`. The product of these index distances is

\[
\prod_{0\le j<k,\ j\ne i}|i-j|=i!(k-1-i)!\mid(k-1)!.
\]

Consequently, if `S` is the sum of `v(n-j)` over the other offsets, then `S ≤ v((k-1)!)`. Taking valuations in

\[
\prod_{j=0}^{k-1}(n-j)=k!\binom nk
\]

gives `M + S = v(k) + v((k-1)!) + v(choose(n,k))`. Because `v(k) ≥ 1`, this forces `v(choose(n,k)) < M`. Thus `n-i` cannot divide the binomial coefficient.

The implementation explicitly verifies the nonzero hypotheses of all factorization identities, handles the empty side of the distance product at either endpoint, and uses a finite maximum. No numerical sampling enters this argument.

## Prior work and attribution

The mathematical observation is attributed to P. Erdős and J. L. Selfridge, *Problem 6447*, American Mathematical Monthly 90 (1983), p. 710, in the pinned Formal Conjectures source. The original journal text was not accessed in this project. This is a formalization of known mathematics, not a mathematical discovery claim.

Existing prize submissions [#56](https://github.com/TheJustinSunPrize/awards/pull/56), [#154](https://github.com/TheJustinSunPrize/awards/pull/154), and [#406](https://github.com/TheJustinSunPrize/awards/pull/406) prove upper-bound constructions with special starting points. Their public Lean sources were inspected; they do not supply the universal arbitrary-`n` conclusion used here. An earlier [Aristotle result](https://github.com/kavanaghpatrick/aristotle-math-problems/blob/2425339a625bf9e9edef22efee04471db6562bcb/submissions/nu4_final/slot568_erdos1063_exception_informal_result.lean) contains partial valuation arguments and special cases, but does not complete this universal theorem. It was inspected, not independently compiled. No code from that result was incorporated in this packet.

No earlier complete formal proof of this exact universal conclusion was located in the bounded search. That search does not establish first priority, and this packet makes no unqualified first-formalization claim. Mathematical correctness, attribution, novelty of the formal contribution, and prize eligibility are separate review questions.

**Gott-L** proposed and initiated the project, set its overall objectives and research direction, and owns and authorizes this submission. **OpenAI Codex** developed the displayed proof, wrote the Lean implementation and documentation, and performed the internal checks under Gott-L's instructions. Earlier mathematical and formalization contributors retain the credit described above. Internal agent review is not independent human review or official prize verification.

## Reproduction

The environment is pinned to Lean `4.19.0` and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` (tag `v4.19.0`). All transitive package revisions are recorded in `lake-manifest.json`.

The source modules are `MaxValuation.lean`, `OffsetProduct.lean`, and `Erdos1063.lean`. The first two prove the valuation and distance-product ingredients; the last combines them and exposes the exact compatibility endpoint.

All three local proof modules compiled successfully in a fresh temporary directory with warnings treated as errors. Ten named axiom audits passed; the endpoints depend only on the standard `propext`, `Classical.choice`, and `Quot.sound` axioms. There are no unfinished proofs, native-decision shortcuts, custom axioms, or unsafe declarations in these source modules. The [verification receipt](verification.json) records the exact source hashes and outcomes. [Internal review](offset-review.md) includes a separate replay of the final theorem.

With the pinned Lean toolchain installed, fetch the pinned dependencies and their Mathlib cache, then run:

```text
lake update
lake exe cache get Mathlib.Data.Nat.Factorization.Basic Mathlib.Data.Nat.Choose.Basic Mathlib.Data.Nat.Factorial.BigOperators Mathlib.Data.Finset.Max Mathlib.Data.Nat.Dist
python verify.py
```

`verify.py` uses Lake to locate the dependency environment, copies only the three local source modules to a new temporary directory, excludes old project build products from the import path, compiles the modules in order, checks both endpoint types, and rejects nonstandard axiom dependencies such as `sorryAx`. The pinned dependency cache is trusted as the normal Mathlib environment; this is not a from-source rebuild of Mathlib, a separately implemented kernel check, or official prize verification. A normal `lake build` is also available.

## License

The new Lean proof code is available under Apache-2.0. Documentation is available under CC BY 4.0. Mathlib and other dependencies retain their own licenses. No dependencies or private contact or payment information are included in the public source packet.
