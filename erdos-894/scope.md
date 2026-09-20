# JSP-000745 / Erdős 894 — independent target-scope review

Reviewed 2026-09-20 by Codex B, a member of the same project team. **Scope verdict: PASS for the proposed statement below.** This is a semantic review of the intended target, not an official review, a build result, or proof verification.

## Intended complete target

For every sequence `a : ℕ → ℕ` such that every `a k > 0` and
`∃ ε : ℝ, 0 < ε ∧ ∀ k, (1 + ε) * (a k : ℝ) ≤ (a (k + 1) : ℝ)`,
prove
`∃ N : ℕ, 0 < N ∧ ∃ c : ℤ → Fin N, ∀ x y : ℤ, ∀ k : ℕ,
  y - x = (a k : ℤ) → c x ≠ c y`.

This covers the full finite-coloring question of JSP745/E894. No scope deficiency was identified.

- **All sequence terms:** the uniform growth condition applies to every index; the result must avoid every term simultaneously, not merely each finite prefix. Positive terms and ε > 0 imply strict increase. Indexing from zero instead of one is harmless.
- **Growth convention:** the paper uses strict growth `>`; the problem page uses `≥`. These define the same class when the positive growth constant is existential: replace ε by ε/2 to obtain strict growth. The proposed weak inequality is not an added restriction.
- **All integers:** the graph in the original paper has vertex set ℤ. The proposed coloring includes zero and negative integers. The E894 webpage's displayed ℕ version follows by restriction; its explanatory text also explicitly identifies the graph on ℤ.
- **Both signs of differences:** because x and y are universally quantified, exchanging them covers the opposite orientation. The implication using positive `y - x = a k` is exactly the undirected adjacency requirement `|x - y| ∈ range a`. Positivity excludes loops.
- **Finite, nonempty colors:** an existential positive N and `Fin N` suffice. The question does not require a particular explicit bound, an optimal dependence on ε, or one universal number of colors for all sequences.

## Sources and the stronger results they distinguish

The [fixed official JSP745 entry](https://github.com/TheJustinSunPrize/awards/blob/cdec393dd0447e8be11f5d2117e165f79e4154bb/problems/catalog-0701-0800.md#JSP-000745) asks for finite coloring of the integers avoiding prescribed lacunary differences. Its references include Katznelson (2001) and Peres–Schlag (2010).

[Peres–Schlag, arXiv:0706.0223v1](https://arxiv.org/pdf/0706.0223v1), page 1, **Problem A**, explicitly asks only whether the corresponding graph on ℤ has finite chromatic number. **Problem B** on that page asks a separate Diophantine question. Page 2, Theorem 1.1, gives the stronger quantitative color bound of order ε⁻¹|log ε| for small ε. Neither that estimate nor optimality of its logarithmic factor is a further obligation of Problem A. Page 3's elementary high-ratio subsequence/product-color argument is expressly presented as a proof of finiteness. A larger finite bound remains a complete answer to JSP745.

The [E894 problem-page search excerpt](https://www.erdosproblems.com/894) agrees: its main question is existence of finite coloring, while the quantitative bound appears in commentary and its link to E464 identifies the separate rotation problem. [Yuval Peres's own problem page](https://www.yp-open-problems.com/erdos-problems-on-lacunary-sequences/) separately states Problems A and B and asks about the logarithmic term afterwards. Do not describe the new target as also settling E464 or proving the best quantitative bound.

## Actual reading and limits

This review read the fixed official catalog entry through the GitHub API; the original-paper abstract and Introduction, pages 1–3, including Problems A/B, Theorem 1.1, and the elementary finiteness argument; and Peres's own problem-page body. Direct web retrieval of E894 returned HTTP 403 and its `/latex/894` endpoint failed, so this review uses the primary-site indexed problem text and the successfully read author manuscript, not a claimed fresh full-page/LaTeX download. Later sections proving the quantitative estimates were not audited.

No new Lean file was inspected or compiled in this semantic review. The completed implementation must still establish the displayed target without missing suppliers or extra assumptions. Known complete prior formalizations, including PR344, remain disclosed in STATUS.md; this review makes no first-formalization or prize-entitlement claim. The reviewer previously read prior E894 formalization code during candidate screening, so this is not a clean-room or independent-discovery certification. No problem-specific Lean source was copied or edited here.
