# Internal statement and proof review

Date: 2026-09-17. The reviewer is a sibling Codex agent in the same assistant/tool environment. This is an internal source review and compiler replay, not independent human peer review or official prize acceptance. The reviewer authored `OffsetProduct.lean` and therefore does not claim an independent review of that component. The main argument in `Erdos1063.lean` and the valuation lemmas in `MaxValuation.lean` were written by other agents.

## Exact statement and scope

`Erdos1063.exists_exception_of_le` proves that for all natural numbers `n,k` with `2 <= k <= n`, some offset `i < k` satisfies `(n-i)` does not divide `n.choose k`. It is a universal theorem, not a bounded numerical verification. The assumptions ensure that every block entry and the binomial coefficient are positive, so the proof does not misuse the convention for the factorization of zero.

`Erdos1063.erdos_1063.variants.exists_exception` specializes this to the public variant's hypotheses `2 <= k` and `2*k <= n`, retaining its namespace and theorem type. The theorem does not assert asymptotic estimates, does not resolve the full JSP-000883 catalogue question, and does not establish mathematical novelty or first-formalization priority. No previously incomplete theorem from Formal Conjectures is imported as an assumption.

## Mathematical checks

The proof chooses a prime divisor `p` of `k`, then chooses a block entry `n-i` having maximum `p`-factorization exponent `M`. For every other entry `n-j`, a common power of `p` divides their nonzero distance; reflection inside the same interval identifies this distance with `|i-j|`. The maximum hypothesis is used in the correct direction.

The offset-product lemma identifies the product of all these distances exactly with `i! * (k-1-i)!`. This product divides `(k-1)!`, so the sum of the remaining block exponents is at most the exponent of `(k-1)!`. Both endpoint offsets and their empty products are covered by the induction.

The proof then uses the identities `n.descFactorial k = k! * choose(n,k)` and `k! = k * (k-1)!`. If the maximizing entry divided the binomial coefficient, its exponent would be at most the binomial exponent. Together with the strict positivity of the exponent of `k`, these equations contradict the preceding upper bound. The final arithmetic contradiction therefore has the required inequality direction and proves the stated nondivisibility.

## Actual verification

Using Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`, the reviewer compiled `OffsetProduct.lean` and independently replayed `Erdos1063.lean` against the compiled local dependencies. Both commands exited with code 0 and no warnings. The main replay did not overwrite another agent's object file. Equivalent commands in a configured project are:

```text
lake env lean -s 65536 -o .lake/build/lib/lean/OffsetProduct.olean OffsetProduct.lean
lake env lean -s 65536 Erdos1063.lean
```

The three audited offset lemmas and both audited main endpoints each reported exactly `[propext, Classical.choice, Quot.sound]`. No `sorryAx` or extra computation axiom appeared. These are standard logical axioms; the certificate is not described as axiom-free.

Reviewed source SHA-256 values:

```text
Erdos1063.lean  afc8f3291c91351165dbccaf641f23d8cc81a61664f8435ed7e385f098863342
MaxValuation.lean  66e32302bd59ee29a90dfd4c153533722d3b7fb17efb5feb15d83c3fbe4f45c0
OffsetProduct.lean  5da16eeca986e223efe9f1992c29a2fcf17e1b3e5a98feae81f76ac6544447f9
```

The semantic review found no gap in the stated auxiliary theorem. Prize eligibility and any broader originality assessment remain separate from these mathematical and compiler checks.
