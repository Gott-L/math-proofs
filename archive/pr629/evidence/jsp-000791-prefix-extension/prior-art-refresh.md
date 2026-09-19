# Bounded prior-source refresh for finite-prefix extension

Review date: **17 September 2026, 11:38:48–11:40:07 UTC**.

**Finding:** this bounded refresh did not locate a previously published complete Lean proof of the exact finite-prefix extension theorem supplied by this package. This is a search result with stated limits, **not** a certificate of global first formalization, mathematical novelty, award eligibility, or organizer acceptance.

This note was prepared by the same internal Codex agent that authored this package's `E951Weights.lean`. The other development agents are part of the same internal AI-assisted workflow. This is not independent human review or organizer-designated verification, and it is not a fresh proof audit of all external projects.

## Exact endpoint compared

The package's `E951.finite_prefix_extension` extends every finite strictly increasing list of real generators greater than one whose monomials are separated by at least one for **all distinct natural exponent vectors**. The resulting infinite strictly increasing sequence preserves that prefix and satisfies the same condition for every pair of distinct finitely supported exponent vectors.

This includes multiplicative injectivity: distinct exponent vectors cannot give equal products. It has no assumed extension step, finite exponent cutoff, or assumed positive-measure conclusion in its final statement. The endpoint is the complete **known extension theorem**, not the eventual prime-counting conjecture of Erdős 951, not a numerical three-generator lower bound, and not a new finite counterexample.

## Fresh official collection and focused queries

The authenticated GitHub collection request was:

`repos/TheJustinSunPrize/awards/pulls?state=all&sort=created&direction=desc&per_page=25`.

It returned the newest 25 PR records, from PR677 back to PR649. All seven new PR bodies after PR670 were read:

| PR | Actual subject of the submitted endpoint |
| --- | --- |
| [671](https://github.com/TheJustinSunPrize/awards/pull/671) | E1100: consecutive coprime divisors versus distinct prime factors |
| [672](https://github.com/TheJustinSunPrize/awards/pull/672) | Bounded Catalan-conjecture verification through 50 |
| [673](https://github.com/TheJustinSunPrize/awards/pull/673) | E1188: counting covering systems without minimality |
| [674](https://github.com/TheJustinSunPrize/awards/pull/674) | E320: compatible-prime extension for reciprocal subset sums and exact doubling |
| [675](https://github.com/TheJustinSunPrize/awards/pull/675) | E1207: distinct distances imply an isosceles-free set |
| [676](https://github.com/TheJustinSunPrize/awards/pull/676) | E396: a Catalan/binomial divisibility component |
| [677](https://github.com/TheJustinSunPrize/awards/pull/677) | E776: antichain multiplicity thresholds |

None describes separated real multiplicative systems or their finite-prefix extension. In particular, the word “extension” in PR674 concerns a different operation and problem. The unrelated seven packages were not downloaded or recompiled; this table is topic triage, not an endorsement of their proofs.

Focused PR searches, with a limit of 20 results and all states, used:

- Official repository: `"951"`, `"000791"`, and `"extension" "000791"`. Each found the already known PR670, with no other matching result.
- Formal Conjectures repository: `"extension" "951"`. No matching PR was returned.
- Global PR query: `"Beurling" "extension"`. Returned material was unrelated to this extension theorem.

Public code queries used `"Erdos951"` (40-result cap), `"finite_prefix_extension"` (20-result cap), and `"Beurling" "extension"` (20-result cap). The exact theorem-name query found unrelated Riemann-hypothesis computation files; the broader Beurling query mostly found transform/quasiconformal results. The E951 query returned the previously inspected sources and statement/index copies described below, rather than a new extension implementation. Primary-GitHub web searches for `"951" "finite" "extension" "Lean"` and `"000791" "extension"` produced no relevant additional source.

These search interfaces are not exhaustive. Index lag, incomplete phrase matching, unpublished work, different terminology, and unindexed branches remain possible. Earlier broad queries in this investigation sometimes missed known files, so an empty result is not treated as proof of absence. No anonymous API rate-limit barrier was retried.

## PR670: unchanged pinned, different complete endpoint

The fresh metadata request for [official PR670](https://github.com/TheJustinSunPrize/awards/pull/670) returned the unchanged head

`zilan520/awards@93d3527ead83a384fbbb9bff95291a27fb56e8df`,

last updated `2026-09-17T11:04:15Z`. The [pinned package](https://github.com/zilan520/awards/tree/93d3527ead83a384fbbb9bff95291a27fb56e8df/submissions/jsp-000791-three-generator) was read in full earlier the same day, before developing this extension. Its entire project-local proof dependency chain is:

1. [`SequenceBridge.lean`](https://github.com/zilan520/awards/blob/93d3527ead83a384fbbb9bff95291a27fb56e8df/submissions/jsp-000791-three-generator/SequenceBridge.lean)
2. [`SharpLower.lean`](https://github.com/zilan520/awards/blob/93d3527ead83a384fbbb9bff95291a27fb56e8df/submissions/jsp-000791-three-generator/SharpLower.lean)
3. [`LowerCertificate.lean`](https://github.com/zilan520/awards/blob/93d3527ead83a384fbbb9bff95291a27fb56e8df/submissions/jsp-000791-three-generator/LowerCertificate.lean)
4. [`ThreeGenerator.lean`](https://github.com/zilan520/awards/blob/93d3527ead83a384fbbb9bff95291a27fb56e8df/submissions/jsp-000791-three-generator/ThreeGenerator.lean), followed only by Mathlib imports.

The final declaration `JSP791.sequence_third_generator_gt_cutoff` proves that every admissible infinite sequence has third generator greater than `4.309405275`. Its strong exponent-vector separation definition and three-coordinate embedding are genuine; its lower bound does not assume only bounded separation. However, none of the four modules constructs a new generator or extends a finite prefix. The explicit exclusions in its README are therefore consistent with its actual local source closure. The fresh unchanged head means this earlier full source reading remains applicable. Its Mathlib transitive closure and its published independent-checker logs were not independently replayed in this refresh.

The README assigns its source to the repository MIT license and documentation to the repository content license. This package does not incorporate that implementation.

## Other inspected primary sources and boundaries

- [`rjwalters/lean-genius@dc62f771ed5010abfdb04247dff6143e0e69d3e7`, Erdos951Problem.lean](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos951Problem.lean): the whole module was read earlier on the review date. Its local closure consists of that module and Mathlib imports. It proves linear growth, elementary counting bounds, and that the ordinary primes satisfy the strong separation property. It does not prove arbitrary finite-prefix extension. The fresh code search returned the same pinned source. No claim is made about every unindexed branch or other file in that large repository.
- [`google-deepmind/formal-conjectures@40e7c98697de6f66b8cbdbf641749ab39ed9c152`, 951.lean](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/951.lean): the fresh `main` metadata still resolves to this commit. The entire E951 file was read earlier on the review date. It contains a proved divergence/API lemma; the eventual prime-counting statement and separate Beurling rigidity statement retain `sorry`. It contains no finite-prefix extension declaration. Its `FormalConjecturesUtil` dependency closure was not newly audited, and no completion claim is inferred from its status tags. The file has Apache-2.0 attribution.
- [`daedalus/alphaproof-nexus@4e65a6ca81655f090a3c8dcf9f56e4a38c984f4c`, E951](https://github.com/daedalus/alphaproof-nexus/blob/4e65a6ca81655f090a3c8dcf9f56e4a38c984f4c/problems/erdos/951/Erdos951.lean): the whole file was read earlier on the review date and has an empty proof block. Its statement is not a proof of extension.

No new matching complete proof was found, so there was no newly discovered relevant dependency closure to download or inspect. The source limits above are deliberate; this note does not certify every public E951 file or all of Mathlib.

## Mathematical attribution and permissible conclusion

The extension theorem is already known. [Patrick White + Claude's public working report of 28 July 2026, section 4](https://www.erdosproblemaday.com/report/951) explains a forbidden-interval measure argument and records earlier Barreto–Price finite-counterexample/extension work and the problem-page discussion. That mathematical precedent is credited in this package. The implemented geometric-weight summation is a proof organization for the known theorem, not a claim to have discovered the theorem.

The report is cited as a mathematical source. Its prose and checker code were not copied into this package or assigned a new license. No explicit reusable source license was found on the inspected report/about pages. This note does not validate that report's separate near-optimal numerical upper certificate or its other claims.

The supported conclusion is narrow: **no duplicate complete Lean finite-prefix extension endpoint was located within this refresh and the stated pinned-source readings**. The full Erdős 951 asymptotic question remains outside this package. Catalogue eligibility, official verification, priority, acceptance, and any award decision remain for the organizers.
