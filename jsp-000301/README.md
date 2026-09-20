# Consecutive powerful nonsquares: JSP-000301

This project gives an independently written Lean proof of the complete yes/no
question [JSP-000301](https://github.com/TheJustinSunPrize/awards/blob/0e93024c553ff533692f1b10af5fbe53050ea2b6/problems/catalog-0301-0400.md#JSP-000301).
The answer is **no**: two consecutive positive powerful integers need not include
a square. The classical example is 12167 and 12168.

This is a later formalization of known mathematics, not a new counterexample or
a claim of first formalization. It does not solve the separate counting question
in [Erdős problem 365](https://www.erdosproblems.com/365).

## Exact meaning and proof

A natural number n is powerful here precisely when n > 0 and, for every natural
prime p dividing n, p² also divides n. `IsSquare` is Mathlib's standard predicate;
it is not a new predicate whose meaning is assumed. Consecutiveness means b = a+1.

Every positive square and every positive cube is powerful. If a prime divides
a product, it divides one factor, so a product of two powerful numbers is also
powerful, without any coprimality requirement. Consequently

\[
12167=23^3,\qquad 12168=2^3\cdot39^2
\]

are powerful. Both lie strictly between 110² = 12100 and 111² = 12321, so neither
is a square. One counterexample disproves the universal assertion in this
catalogue entry; no assertion about all consecutive pairs is being inferred
from a finite search.

`Main.lean` proves both the explicit existential statement and the negation of
the catalogue's universal assertion. The named endpoints are:

- `GottL301.exists_consecutive_powerful_nonsquares`
- `GottL301.exists_positive_consecutive_pair`
- `GottL301.not_catalog_claim`
- `GottL301.not_all_consecutive_powerful_have_square`

## An infinite family

The additional construction starts at n₀ = 12167 and iterates

\[
 n_{k+1}=n_k(4n_k+3)^2.
\]

The polynomial identity

\[
 n(4n+3)^2+1=(n+1)(4n+1)^2
\]

shows that both entries in the next pair are the previous entries multiplied
by positive squares. Thus powerfulness is preserved. Also n₀ ≡ 7 (mod 16),
and the recurrence preserves this congruence. Squares modulo 16 are only
0, 1, 4, and 9, so nₖ and nₖ+1, congruent to 7 and 8 respectively, are never
squares. Finally nₖ > 0 and (4nₖ+3)² > 1 show strict increase. Consequently
the construction supplies infinitely many distinct pairs, rather than just
many computed examples.

This argument is an elementary instance of the classical Pell-type
multiplication method. It is an additional formalized conclusion beyond what
the yes/no catalogue question requires, not a new historical theorem, a
classification of all such pairs, or an asymptotic counting formula.
The endpoint in `Family.lean` is
`GottL301Family.infinite_consecutive_powerful_nonsquares`. `Audit.lean` also
restates its conclusion directly in terms of prime divisibility.

## Historical mathematics and earlier formalizations

The classical powerful-number literature includes S. W. Golomb, *Powerful
Numbers*, American Mathematical Monthly 77 (1970), 848–852; David T. Walker,
[*Consecutive Integer Pairs of Powerful Numbers and Related Diophantine
Equations*](https://www.fq.math.ca/Scanned/14-2/walker.pdf), Fibonacci Quarterly
14 (1976), 111–116; and Richard K. Guy, *Unsolved Problems in Number Theory*
(2004). Walker's Section 3 treats the nonsquare/nonsquare case by Pell-type
equations. This package does not determine the first discoverer or date of the
particular numerical example.

Earlier public formalization records include
[issue 63](https://github.com/TheJustinSunPrize/awards/issues/63),
[PR666](https://github.com/TheJustinSunPrize/awards/pull/666), and
[PR669](https://github.com/TheJustinSunPrize/awards/pull/669).
They were known before this implementation. PR669 already advertises a Lean
4.19 proof of the finite counterexample, so compatibility with that version is
not claimed as a previously missing contribution. No problem-specific Lean
code from those implementations is copied or imported in this package. This
is not a clean-room claim, and the bounded prior-work check is not exhaustive.

Gott-L initiated this project, set its objectives, and directed the research.
Codex reconstructed the arguments, wrote the Lean implementation, and performed
internal checks. Internal reviewers belong to the same project team and are
not official prize reviewers or independent human verifiers. Historical
mathematical credit and earlier formalization priority remain with their authors.

## Reproduction

The project pins Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b`. With those dependencies available,
run `lake build` and `lake env lean Audit.lean`. To save both outputs and their
exit codes, run `python verify.py --label my-check`. The local compilation helper uses the existing pinned Mathlib
cache; the verification record distinguishes that process from rebuilding all
dependencies from source. See `VERIFICATION.md` for completed checks and their
limits.

The package must be judged on its actual statement and evidence. Publication,
compilation, or a catalogue reference does not establish official acceptance,
priority, candidate status, or an award. It makes no claim for the mathematical
solver role for the historical result.
