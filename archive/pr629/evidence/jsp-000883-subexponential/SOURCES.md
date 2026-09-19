# Sources, attribution, and reuse

This package is a formalization contribution based on existing mathematical work. Its arbitrary-degree argument extends a particular fixed-rate Lean proof; it makes no claim of mathematical discovery or global first formalization. The references below distinguish code reused under a stated license from mathematical background and sources whose full contents were not obtained.

## The directly reused Lean proof

[The Justin Sun Prize PR601](https://github.com/TheJustinSunPrize/awards/pull/601), by **56647563**, is pinned here to:

- Repository: [`56647563/awards`](https://github.com/56647563/awards).
- Commit: [`5130380a1d7f3ed00b827c666c79c89e202c3fdc`](https://github.com/56647563/awards/tree/5130380a1d7f3ed00b827c666c79c89e202c3fdc/submissions/jsp-000883).
- Source directory: `submissions/jsp-000883`.
- License for its Lean source: Apache-2.0, retained in [LICENSE](LICENSE).

That source attributes its formalization to 56647563 with Codex assistance. Its completed endpoint is the eventual upper bound `n_k ≤ exp((3/4) log(2) k)` and the associated improved-upper target. Its finite carry, anchor, exceptional-index, simultaneous-box, and coarse size arguments supply the basis of this package.

`OneCarry.lean`, `FiniteConstruction.lean`, and `Simultaneous.lean` are adaptations of that code. `SizeBounds.lean` retains its coarse finite bound while using the local exact prime-count definition. `SubexpParameters.lean` and `SubexpAsymptotic.lean` extend its parameter and asymptotic argument from degree 16 to an arbitrary fixed degree chosen after ε. Compatibility changes and original/adapted hashes are recorded in [compatibility-notes.md](compatibility-notes.md) and [port-metadata.json](port-metadata.json).

The new primitive prime-count estimate and the compatibility/infimum bridges are identified in their source headers. Reuse of an already completed finite proof is not presented as newly solving those finite lemmas.

## Patrick White's written construction

Patrick White's [erdos1063-upper-bound repository](https://github.com/pw/erdos1063-upper-bound/tree/a28481f5b4bda374086533397269c5b550c759b8), pinned to `a28481f5b4bda374086533397269c5b550c759b8`, presents a stronger written bound of the form

`n_k ≤ exp(C*k*log log k/log k)`

for sufficiently large k. Thus the mathematical subexponential conclusion predates this package. Its [README](https://github.com/pw/erdos1063-upper-bound/blob/a28481f5b4bda374086533397269c5b550c759b8/README.md) credits GPT-5.6 Sol via Codex for the construction and describes a Claude-assisted computational check, with Patrick White and Claude/MathDyad attribution.

The bounded inspection of this revision found written mathematics, a Python checker, and a log, rather than a Lean proof. That observation concerns the inspected revision only; it does not establish the absence of other formalizations. No license file was found in that inspection. This package does not copy its code or substantial prose. The reused Lean code instead comes from the explicitly licensed PR601 source above.

## Ricky Cipollini's related work: access limitation

PR601 cites Ricky Cipollini's related work through the [Erdős 1063 proof-claims page](https://www.erdosproblems.com/forum/thread/1063/proof-claims) and the [linked Overleaf manuscript](https://www.overleaf.com/read/hrpsqsnqktky). Its attribution identifies Cipollini and GPT-5.6 Sol; that attribution is retained here.

The full Overleaf manuscript and its license were not obtained in this workflow. We therefore do not certify its exact theorem, proof details, relationship in priority to White's work, or absence of a separate Lean formalization. It is a relevant prior-work reference, not a document silently treated as having been fully reviewed or licensed for reuse.

## Problem statement and minimum

The definition follows [Formal Conjectures, Erdős 1063](https://github.com/google-deepmind/formal-conjectures/blob/cb20d7eb22b6f9866001d53fdf1ea4bb93fb34c0/FormalConjectures/ErdosProblems/1063.lean), pinned to commit `cb20d7eb22b6f9866001d53fdf1ea4bb93fb34c0`.

That file is copyright 2026 The Formal Conjectures Authors, Apache-2.0. It defines the minimum as a natural `sInf` over blocks with exactly one nondivisor and the lower bound `2k ≤ n`. The package preserves that meaning and establishes nonemptiness before using membership of the minimum. Its `better_upper` comparator uses a natural-number LCM before casting to reals; this package's subexponential endpoint is stated directly in terms of n and its logarithm.

The broader question and historical references are available on the [Erdős Problems page](https://www.erdosproblems.com/1063). This package does not claim the exact value or sharp asymptotic order of the minimum.

## Mathlib and classical ingredients

The environment uses Lean 4.19.0 and Mathlib commit [`c44e0c8ee63ca166450922a373c7409c5d26b00b`](https://github.com/leanprover-community/mathlib4/tree/c44e0c8ee63ca166450922a373c7409c5d26b00b), with its Apache-2.0 license and file-level author notices.

- [`Mathlib/NumberTheory/Primorial.lean`](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/NumberTheory/Primorial.lean), by Patrick Stevens and Yury Kudryashov, supplies `primorial_le_4_pow`. `PrimeCountBound.lean` derives the coarse bound `π(k) log k ≤ 6k` from it.
- [`Mathlib/Data/Nat/Multiplicity.lean`](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Data/Nat/Multiplicity.lean), credited to Chris Hughes, formalizes the classical Legendre and Kummer multiplicity/carry results. `CarryCompatibility.lean` derives the newer factorization interface used by PR601 from `Nat.Prime.emultiplicity_choose` in this pinned version.
- [`Mathlib/Data/Nat/Choose/Factorization.lean`](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Data/Nat/Choose/Factorization.lean), by Bolton Bailey, Patrick Stevens, and Thomas Browning, provides binomial factorization infrastructure.
- [`Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean) supplies logarithm inequalities and `Real.isLittleO_log_id_atTop`. The proof uses this elementary real asymptotic, rather than the prime number theorem.

The classical mathematical results and their Mathlib implementations retain their original attribution. The separate El Bachraoui short-prime-interval route explored during research is not used in this package.

## Roles and review boundary

Gott-L: project initiation, objectives, planning, and research direction. Codex assistance: compatibility work, new formalization, mathematical checks, and documentation. Original formalization and mathematical authors remain credited as above.

These are authoring-workflow checks, not independent external peer review. This document records provenance; it does not assert an award, an eligibility decision, an official acceptance, a payment amount, or a global priority finding.
