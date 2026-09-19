# Internal semantic review and separate replay

**Result: passed.** All five frozen proof modules were recompiled in a fresh directory, with old project-local compiled modules excluded. Twelve independently transcribed statement or edge-case checks passed, followed by transitive axiom audits of all 34 named public definitions/theorems and all 12 review statements: 46 audits in total. Each uses only a subset of `propext`, `Classical.choice`, and `Quot.sound`. No proof source was changed for this review.

The machine-readable result is [review-a/receipt.json](review-a/receipt.json); the review statements are [review-a/Audit.lean](review-a/Audit.lean), and the named audits are [review-a/AxiomAudit.lean](review-a/AxiomAudit.lean). This was a separately written review harness, [review_full_a.py](review_full_a.py), not simply another invocation of the primary verifier.

## Participation and trust boundary

This reviewer is a Codex agent in the same collaborating AI team. It authored `E336Defs`, `E336Padding`, and `E336Necessity`, and did not author `E336Differences` or `E336Criterion`. Therefore the review is internal cross-module checking with disclosed author participation. It is not an external human review or a wholly independent verification of the entire development. Gott-L directed and coordinated the project; Codex implemented the formal proofs.

The replay used Lean4.19.0 with stack size65536 and warnings treated as errors. All nine dependency checkout commits matched `lake-manifest.json`, and all nine had clean tracked source files. Their Git tree hashes and configuration-file SHA256 hashes are recorded in the receipt, together with the manifest, toolchain-file and Lean-executable hashes. Existing pinned dependency compiled files and the Lean toolchain remain trusted; Mathlib was not rebuilt, and this review did not use a separate external proof checker. The external-checker work on the earlier JSP-000399 packet does not validate this packet.

## Mathematical and semantic findings

**The actual gcd condition constructs the certificate.** `BalancedDifference A z` means the difference of the sums of two concrete finite lists of members of `A`, with equal lengths. The integer codomain is essential: subtraction does not silently truncate. Concatenation, interchange and repeated concatenation establish addition, negation and multiplication by natural numbers. Every pairwise natural distance is represented by appropriately ordered singleton lists.

The common-divisor condition ensures a positive balanced difference exists; otherwise every distance would be zero and zero itself would be a common divisor, contradicting the condition. The proof chooses the least positive natural balanced difference `d`. The difference `v - (v/d)*d` is again balanced and equals the nonnegative remainder `v % d`. Minimality and `d > 0` force that remainder to vanish. Applied to each pairwise distance, this makes `d` a common divisor and hence one. The finite lists witnessing one are retained throughout the argument. No Bézout certificate, a preexisting exact order, or a gcd-extraction theorem is assumed.

The gcd condition also makes `A` nonempty. Scaling the balanced difference one by a chosen `a ∈ A` yields equal-length lists whose sums differ by `a`. Appending `a` to the smaller-sum list gives exactly equal sums and lengths `L,L+1`. This remains correct when `a=0`; an empty shorter list is allowed.

**The eventual count is uniform.** Given a variable representation length `j ≤ r`, the padding proof uses `j` short copies and `r-j` long copies. Their total sum is `r*M`; their length is `r*(L+1)-j`. After the original representation is appended, the exact count is the single number `r*(L+1)`, independent of the target integer. If the weak threshold is `N`, the threshold `N+r*M` ensures natural subtraction of `r*M` is legitimate. Zero-term weak representations and zero-valued summands are included.

**Necessity uses genuine equal-length representations.** Divisibility of all pairwise distances gives congruence of sums of lists of the same length. Representations of `N` and `N+1` force the common divisor to divide one. This direction does not require an extra weak-basis premise or an independently chosen element of `A`.

**The final equivalences have the intended quantifiers.** The set endpoint assumes only the stated weak-basis bound. Its sufficient direction calls the proved arithmetic construction and the proved padding lemma, closing the finite-certificate premise. A successful fixed count then gives a least successful count by natural well-ordering, with minimality against every smaller natural number. The additional positivity theorem rules out exact count zero.

The sequence endpoint requires a strictly increasing natural-number sequence and takes `A` to be exactly its range. Consecutive differences use natural subtraction, which is correct because of monotonicity. Inductive congruence with the first term proves equality of the sets of common divisors for consecutive and pairwise differences. The gcd-one condition is the ordinary universal common-divisor property; no custom gcd function with unproved meaning is substituted.

The weak-basis premise is essential: a finite set can have difference gcd one without admitting any uniformly bounded representation length for all large numbers. The theorem never omits that premise. Strict increase in the sequence form gives an infinite range; the set form need not redundantly assume infinitude, since being a bounded-summand asymptotic basis already excludes finite sets.

## What the twelve review statements check

- Fully expanded set and sequence statements, including least-order minimality.
- Fully expanded unconditional sufficient and necessary directions, with the actual all-divisors condition.
- Construction of concrete equal-sum adjacent-length lists and of a balanced difference equal to one.
- The uniform padding count and the pairwise/consecutive common-divisor equivalence.
- Positivity of an eventual exact count.
- Explicit repeated-summand and zero-summand representations, and impossibility of eventual count zero.

The raw final statements contain no project predicate aliases for their main representations, no `AdjacentLengths` hypothesis, and no assumed arithmetic extraction. The small repetition and zero witnesses intentionally use the project representation predicate to check that its list semantics permit those cases.

The first replay passed all five proof modules but two review-only singleton-set witnesses needed explicit definitional equality instead of a simplifier call. The Windows review-output encoding also required correction. Only the audit/harness changed; a final complete fresh replay passed. These were review-source issues, not changes to or gaps in the mathematical proof.

## Scope and documentation

The original source is Erdős–Graham (1980), Theorem1, pp.202–203. This implements that known full characterization. It does not solve the separate E336 extremal-limit question, prove an optimal bound in `r`, or establish first formalization worldwide. `README.md`, `PROOF_OUTLINE.md`, `SOURCES.md`, and `NOTICE` were checked against the actual proof and receipts and maintain that distinction. They acknowledge PR660, the large existing plby development, the inspected rjwalters source, and the catalogue's `Eligible to claim: No` record.

Publication, official prize review, eligibility, and payment remain separate from local proof checking. This report contains no private contact or payment information.

Documentation licensed CC BY4.0; review code licensed Apache-2.0. Exact frozen-source hashes are recorded in the linked receipt.
