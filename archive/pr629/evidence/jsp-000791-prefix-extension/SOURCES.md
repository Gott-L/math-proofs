# Sources, attribution, and scope

This file records the mathematical sources and bounded prior-source review behind the finite-prefix extension package. Repository pins identify inspected versions; they are not claims that those external projects were rebuilt or independently certified here. No global mathematical or formalization priority is asserted.

## Mathematical sources

1. **Barreto–Price; Patrick White with Claude.** The [Erdős Problem a Day working report for problem 951](https://www.erdosproblemaday.com/report/951), dated 28 July 2026, discusses finite-prefix extension in §4 and credits earlier Barreto–Price work. It describes a forbidden-interval measure argument followed by iteration. Its concluding scope discussion distinguishes extension from the eventual prime-counting problem. The report links a [Barreto–Price note](https://drive.google.com/file/d/1CRBMOMCTdAuuVp8Wqace1AQ_dpK9BeTV/view); that linked note was not accessible during this review, so its full contents were not independently inspected. Attribution to it here follows the accessible report.

   The present implementation gives a fresh proof using inverse-square-root monomial weights, geometric series, and the window `[S², 2S²]`. It does not copy the report's prose or numerical checker, and makes no priority claim for this variation of the known argument. The source's White-and-Claude attribution is retained.

2. **Formal Conjectures statement.** The inspected statement is [`google-deepmind/formal-conjectures@40e7c98697de6f66b8cbdbf641749ab39ed9c152`, `FormalConjectures/ErdosProblems/951.lean`](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/951.lean). Its separation condition quantifies over distinct finitely supported natural exponent vectors. The main counting assertion is **eventual**, not an inequality demanded at every real cutoff. The inspected file leaves that assertion and a separate Beurling rigidity conjecture admitted, while proving a supporting divergence/API result. This package does not fill either admitted main statement and does not import this file.

## Existing formal material and the selected endpoint

- [Official PR670](https://github.com/TheJustinSunPrize/awards/pull/670), pinned to [`zilan520/awards@93d3527ead83a384fbbb9bff95291a27fb56e8df`](https://github.com/zilan520/awards/tree/93d3527ead83a384fbbb9bff95291a27fb56e8df/submissions/jsp-000791-three-generator), provides a different endpoint: `JSP791.sequence_third_generator_gt_cutoff`, namely `4.309405275 < a 2` under the full sequence separation hypothesis. The four project-local files `SequenceBridge.lean`, `SharpLower.lean`, `LowerCertificate.lean`, and `ThreeGenerator.lean` were inspected. Their final bridge has no finite exponent cutoff. The extension theorem is outside that inspected dependency chain. No PR670 proof code was copied into this package.

- [`rjwalters/lean-genius@dc62f771ed5010abfdb04247dff6143e0e69d3e7`, `Erdos951Problem.lean`](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos951Problem.lean) was inspected for its actual declarations. It contains elementary growth/counting material and an ordinary-prime example, but no finite-prefix extension theorem in the inspected file.

- [`daedalus/alphaproof-nexus@4e65a6ca81655f090a3c8dcf9f56e4a38c984f4c`, `Erdos951.lean`](https://github.com/daedalus/alphaproof-nexus/blob/4e65a6ca81655f090a3c8dcf9f56e4a38c984f4c/problems/erdos/951/Erdos951.lean) is an unfinished proof stub at the inspected pin.

These inspections support choosing the extension theorem as a distinct endpoint from the particular sources reviewed. They do not establish that no other complete implementation exists. No external repository replay is claimed by this source audit.

## Library and implementation provenance

The implementation targets Lean 4.19 and [`mathlib4@c44e0c8ee63ca166450922a373c7409c5d26b00b`](https://github.com/leanprover-community/mathlib4/tree/c44e0c8ee63ca166450922a373c7409c5d26b00b). It uses Mathlib's real square roots, finite products, geometric-series and `HasSum` infrastructure, nonnegative extended-real sums, Lebesgue interval measures, and countable subadditivity. Relevant source entry points include:

- [`Mathlib/Analysis/SpecificLimits/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Analysis/SpecificLimits/Basic.lean);
- [`Mathlib/Analysis/Normed/Ring/InfiniteSum.lean`](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/Analysis/Normed/Ring/InfiniteSum.lean);
- [`Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/c44e0c8ee63ca166450922a373c7409c5d26b00b/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean).

Mathlib's existing author and Apache-2.0 notices remain applicable to its code. The local modules are a new implementation of the cited mathematics. Gott-L supplied project initiation, conception, objectives, planning, and research direction. Codex assisted with mathematical research, implementation, and internal checks. These project roles do not transfer mathematical discovery credit from the cited authors.

The internal mathematical review was performed within the authoring team, including the agent that wrote `E951Intervals.lean`. It checked the exponent-vector quantifiers, empty prefix, all positive new exponents, countable union, and finite-to-infinite product bridge. It is not an independent external review, an official prize decision, or a substitute for verification records.

## Prize and licensing boundary

At the inspected official catalogue pin [`TheJustinSunPrize/awards@f4e7173d89dfe91022a185427d63452c8ffbf6ae`](https://github.com/TheJustinSunPrize/awards/blob/f4e7173d89dfe91022a185427d63452c8ffbf6ae/problems/catalog-0701-0800.md), JSP-000791 is marked **Eligible to claim: No**. Formalizing an associated known theorem does not itself create eligibility, official acceptance, or an award entitlement. This package supplies no proof of the catalogue problem's eventual prime-counting conclusion and makes no payment guarantee.

The original prose in this package is licensed under [Creative Commons Attribution 4.0 International](https://creativecommons.org/licenses/by/4.0/), consistently with the package's content license. The new Lean files are Apache-2.0. Cited papers, websites, repositories, and third-party source files retain their own licenses. In particular, this documentation neither relicenses the working report nor incorporates the differently licensed PR670 code.
