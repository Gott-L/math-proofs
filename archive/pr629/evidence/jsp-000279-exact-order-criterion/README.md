# JSP-000279 / Erdős 336: the complete exact-order criterion

This packet formalizes the classical Erdős–Graham (1980) characterization of
when a bounded-summand asymptotic additive basis has a fixed exact order.
It proves the full criterion, including both directions, existence of a least
exact order, and the original consecutive-difference formulation for a strictly
increasing sequence. Summands may repeat and zero is allowed.

## Exact result

Let `A ⊆ ℕ`. Suppose some bound `r` has the property that every sufficiently
large natural number is a sum of at most `r` elements of `A`. Then the following
are equivalent:

1. Some fixed number `h` of elements of `A` represents every sufficiently large
   natural number; consequently a least such `h` exists.
2. The only natural number dividing every distance `|x-y|`, for `x,y ∈ A`, is one.

For `A = range(a)` with `a : ℕ → ℕ` strictly increasing, condition 2 is equivalent
to the usual gcd-one condition on all consecutive differences `a(i+1)-a(i)`.
The code states gcd one by its universal common-divisor property, and proves
the pairwise/consecutive bridge; it does not assume a finite Bézout certificate.

Principal declarations in `E336Criterion.lean`:

- `E336.exists_eventuallyExactly_iff` — fixed-count existence iff gcd one.
- `E336.erdos_graham_set_criterion` — existence of the least exact order iff gcd one.
- `E336.erdos_graham_sequence_criterion` — the strictly increasing sequence version.
- `E336.eventuallyExactly_pos` — an eventual exact order is necessarily positive.

The bounded-basis hypothesis remains essential. A finite set such as `{2,3}`
has difference gcd one but is not a bounded-summand asymptotic basis.

## Proof and scope

The finite arithmetic module proves, from the actual all-divisors condition,
that a single value `M` has representations with lengths `L` and `L+1`.
Padding a variable-length representation with copies of these lists produces
a fixed valid count `r*(L+1)` and threshold `N+r*M`. Minimality is then obtained
by natural-number well-ordering. The reverse implication uses congruence of
equal-length sums and representations of two consecutive large integers.
See [PROOF_OUTLINE.md](PROOF_OUTLINE.md) for the least-positive-difference
construction used in the Lean implementation.

This is a formalization of known mathematics. It does not prove the extremal
limit sought in the main catalogue question or give an optimal bound in `r`.
The catalogue currently records `Progress`, `Lean proof: No`, and
`Eligible to claim: No`; those records are not changed by this evidence packet.
The request concerns assessment of the actual formalization contribution,
including applicable community-contribution or partial-progress provisions.

## Verification and reproduction

Lean 4.19.0 and Mathlib commit
`c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned by the included files.
The five proof modules passed fresh local compilation, 34 named declaration
axiom audits and eight explicit statement/edge-case checks; see
[verification.json](verification.json). All nine dependency checkout revisions
were checked against the manifest. Only `propext`, `Classical.choice` and
`Quot.sound` are permitted; many individual declarations use fewer.

With the pinned Lean toolchain, Python 3 and Git available, use:

```text
lake update
lake exe cache get
python verify.py
```

The verifier compiles local modules in a fresh temporary directory, excludes
old project-local build products from its import path, checks source hashes
and axiom dependencies, and writes a new verification receipt. It uses the
pinned dependency cache; it does not rebuild Mathlib or independently verify
that cache. The cache command above may download more than the selective
shared cache used in development.

The separate internal replay and reviewer participation are recorded in
[internal-review.md](internal-review.md). These are internal checks, not official
prize acceptance or independent human peer review. The external-checker
supplement for JSP-000399 is a different packet and does not verify this one.

## Attribution and prior work

Gott-L initiated the project, set its objectives and research direction, planned
and coordinated the work, and authorizes submission. Codex assisted with source
research, proof development, Lean implementation and internal verification.
The mathematical theorem is due to P. Erdős and R. L. Graham (1980).

The inspected PR660 proves a particular order-two/order-three example. The much
larger `plby/lean-proofs` E336 development asserts an extremal-limit endpoint
under a framework that already includes exact-order hypotheses. Both are
acknowledged in [SOURCES.md](SOURCES.md); their code was not reused here.
The inspected `rjwalters/lean-genius` file describes the gcd criterion in prose
without proving it. Bounded source inspection does not establish worldwide
first priority, and no such priority or award decision is asserted.

Proof code and scripts: Apache-2.0. Documentation: CC BY 4.0. Dependency and
prior-author attribution is preserved in [NOTICE](NOTICE). Private contact and
payment details are excluded.
