# JSP-000883 / Erdős 1063: a subexponential upper bound

This packet extends the fixed exponential-rate formalization in
[PR 601](https://github.com/TheJustinSunPrize/awards/pull/601) to every positive
exponential rate. It formalizes an already public mathematical conclusion;
the mathematical sources are Patrick White and Ricky Cipollini, with their
stated AI collaborators. The reused finite proof retains 56647563's
formalization credit and Apache-2.0 license.

## Exact completed result

Let `Admissible k n` mean `n >= 2*k` and that exactly one of the integers
`n-i`, `0 <= i < k`, fails to divide `Nat.choose n k`. Let `leastWitness k`
be the natural-number infimum of this set, exactly the minimum definition
used in the Formal Conjectures Erdős 1063 statement.

The main endpoint in [SubexpAsymptotic.lean](SubexpAsymptotic.lean) is:

```text
For every real epsilon > 0, for all sufficiently large natural k,
there exists an actual admissible n with n <= exp(epsilon*k).
```

[SubexpSubmission.lean](SubexpSubmission.lean) then proves, without any
additional mathematical hypothesis:

- For every epsilon > 0, eventually `leastWitness k <= exp(epsilon*k)`.
- `log(leastWitness k) = o(k)`.
- `log(leastWitness k) / k` tends to zero.

[SubexpNonempty.lean](SubexpNonempty.lean) separately proves that the admissible
set is nonempty for every `k >= 2`, and that its minimum itself satisfies the
full admissibility predicate. The infimum is never bounded by exploiting an
empty set. The unique exception is proved to fail to divide; it is not an
unchecked coordinate.

This does not determine the sharp order or exact values of the minimum. It
does not claim a new mathematical discovery, worldwide first formalization,
an official award, or completion of every formulation of the broader problem.

## Contribution beyond the existing formalization

[PR 601's fixed source](https://github.com/56647563/awards/tree/5130380a1d7f3ed00b827c666c79c89e202c3fdc/submissions/jsp-000883)
already proves the registered improved-upper target, using the particular
rate `exp((3/4)*log(2)*k)`. Its complete finite construction is reused here.
That earlier result is credited, not claimed again as a new contribution.

The extension makes the root degree an arbitrary integer `d >= 4`, proves
a sufficient elementary prime-count estimate in Lean 4.19, and chooses `d`
after an arbitrary epsilon. This order of quantifiers gives a rate tending
to zero, which a single fixed positive rate does not provide. It also avoids
needing the newer Mathlib Chebyshev module or the prime number theorem.

[PROOF_OUTLINE.md](PROOF_OUTLINE.md) gives the argument;
[SOURCES.md](SOURCES.md) records the bounded prior-art search, exact pins,
licenses, and inaccessible-source limits;
[compatibility-notes.md](compatibility-notes.md) distinguishes the reused
finite proof from the new extension and records the interface adaptations.

## Verification and reproduction

The environment is Lean 4.19.0 with Mathlib fixed to
`c44e0c8ee63ca166450922a373c7409c5d26b00b`; see
[lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), and
[lake-manifest.json](lake-manifest.json). With the pinned toolchain and Python
available, obtain the required dependencies and run:

```sh
lake exe cache get Mathlib.Data.Nat.Choose.Factorization Mathlib.NumberTheory.Primorial Mathlib.Analysis.SpecialFunctions.Log.Basic Mathlib.Analysis.Asymptotics.Lemmas Mathlib.Data.Fintype.Pigeonhole Mathlib.Data.Fintype.BigOperators Mathlib.Data.Nat.Find Mathlib.Data.Nat.Lattice Mathlib.Tactic.FieldSimp Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
python verify.py
```

The verifier compiles all eleven submitted proof modules in a fresh temporary
directory, excludes old project build products, treats warnings as errors,
checks ten explicit statement types, and checks 86 named declarations against
the standard axiom allowlist `propext`, `Classical.choice`, `Quot.sound`.
It rejects proof placeholders, extra axioms, and untrusted native decision
shortcuts. [verification.json](verification.json) records the result and exact
source hashes; [TypedAudit.lean](TypedAudit.lean) records the statement checks.

The recorded fresh compilation, all 86 declaration audits, and all ten type
checks passed. A separate same-team replay also passed all eleven modules,
twelve independently transcribed statement checks, and 98 named audits (86
source declarations plus twelve review statements). Its reviewer ported the
reused finite modules but did not write the new prime-count, parameter,
asymptotic or minimum proofs.

Pinned dependency caches are trusted and are not all rebuilt by this script.
The internal review is described in [internal-review.md](internal-review.md),
including the reviewer's participation in porting the reused finite modules.
These checks are not official organizer verification or independent human
review. Repository structure checks do not execute the Lean proof.

## Attribution and requested review

Gott-L initiated the project and supplied its objectives, planning and research
direction. Codex performed the research, proof extension, implementation,
documentation and internal checks. Patrick White, Ricky Cipollini, their stated
AI collaborators, 56647563 with Codex, the Formal Conjectures Authors, and
Mathlib contributors retain the respective credits documented in the sources.

Please assess the additional subexponential formalization under the official
rules, including contribution or partial-progress provisions where applicable.
Eligibility, priority, award tier and any allocation remain for the organizer.
No catalogue, candidate, recipient-confirmation, award or payment record is
changed. Private contact and payment information are excluded.

Lean code and verification scripts: [Apache-2.0](LICENSE). New documentation:
[CC BY 4.0](LICENSE-CONTENT). See [NOTICE](NOTICE) for attribution.
