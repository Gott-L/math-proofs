# JSP-000791 / Erdős 951: complete finite-prefix extension

This packet formalizes the known theorem that every finite, strictly increasing, strongly separated list of real generators greater than one extends to an infinite list with the same properties. It also proves that a valid next generator can be chosen above any prescribed real cutoff. The extension preserves the original prefix exactly.

The separation condition concerns **distinct exponent vectors**, including zero vectors: any two different finite vectors of natural exponents give products whose distance is at least one. For the infinite sequence, the condition holds for every pair of distinct finitely supported natural exponent vectors. It is not restricted to bounded exponents or to pairs already known to have unequal numerical products.

This is a complete known auxiliary theorem associated with Erdős 951. **It does not resolve the original eventual prime-counting conjecture, prove a near-optimal triple certificate, or construct infinitely many prime-counting violations.** The official catalogue records “Eligible to claim: No.” We request assessment of the actual formalization contribution; no entitlement to an award, global first formalization, or mathematical discovery is asserted.

## Exact endpoints

For `a : Fin n → ℝ`, assume all entries exceed one, `StrictMono a`, and

```text
u ≠ v  →  |∏ i, a(i)^u(i) − ∏ i, a(i)^v(i)| ≥ 1
```

for every pair `u,v : Fin n → ℕ`. The theorem `E951.finite_prefix_extension` produces `b : ℕ → ℝ` with:

1. `StrictMono b` and every entry of b greater than one;
2. `b i = a i` for every original index;
3. the same separation inequality for every pair of distinct finitely supported natural exponent vectors on ℕ.

The empty initial prefix is included. No summability, measure estimate, avoidance witness, or extension-existence assumption remains in the final theorem.

The one-step endpoint `E951.extension_step` proves the next-term existence premise in full. The intermediate recursion theorem `exists_sequence_extension` takes that premise as a parameter; the final endpoint explicitly supplies its proved implementation. `exists_avoiding_above` establishes avoidance of all cross-power collisions above any cutoff, even without the old separation assumption.

## Argument and attribution

The proof sums the reciprocal-square-root weights of all old monomials using finite products of geometric series. On a large interval `[S²,2S²]`, it bounds the outer measure of each forbidden set. Summing the weighted bounds over all exponent vectors and all positive powers gives at most `32 S Z²`, where Z is the finite total weight. Choosing `S > 32 Z²` makes this smaller than the interval length, so a valid new generator exists. A coherent sequence of finite extensions gives the infinite result, and an exact support argument transfers every pair of finitely supported exponents to a common finite stage.

The extension argument is known from work attributed to Barreto–Price and discussed in Patrick White with Claude's public working report. This package uses a fresh geometric-series implementation of that method. The report's code and prose are not copied. The earlier PR670 implements a different, quantitative three-generator lower bound; none of its code is reused here. See [the proof outline](PROOF_OUTLINE.md), [sources and scope](SOURCES.md), and [bounded source refresh](prior-art-refresh.md).

## Reproduction and verification

The project pins Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` in the toolchain and Lake manifest.

```sh
lake update
lake exe cache get Mathlib.Algebra.BigOperators.Fin Mathlib.Data.Finsupp.Basic Mathlib.Data.Real.Sqrt Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Tactic.FieldSimp Mathlib.Analysis.SpecificLimits.Basic Mathlib.Analysis.Normed.Ring.InfiniteSum Mathlib.Topology.Instances.ENNReal.Lemmas Mathlib.MeasureTheory.Measure.Lebesgue.Basic Mathlib.Algebra.BigOperators.Finsupp.Basic
python verify.py
```

Use `python3` if required by the platform. The verifier checks the installed Mathlib revision, copies all seven proof modules into a fresh temporary directory, excludes old project build outputs, compiles with warnings treated as errors, checks six explicit statements, and audits 38 named declarations. The only accepted logical dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

[verification.json](verification.json) records the primary results and source hashes. A separate internal replay passed all seven modules, 12 independently transcribed statements and 51 audits (39 source declarations plus 12 review declarations). Its details are described in [internal-review.md](internal-review.md), with [its receipt](review-a/receipt.json). The reviewer authored the append and sequence modules; that participation is disclosed. Both runs trust the pinned dependency caches and the toolchain rather than rebuilding their bootstrap chains. Internal replay is not official verification or independent external human review.

## Roles and licenses

Gott-L initiated and conceived the project, set its objectives, and provided planning and research direction. Codex assistance performed the source research, formal implementation, documentation and internal checks under those instructions. The historical mathematical argument and Mathlib retain their attribution.

Code is licensed under [Apache 2.0](LICENSE); original documentation is licensed under [CC BY 4.0](LICENSE-CONTENT). See [NOTICE](NOTICE). Publication does not establish official acceptance, a prize decision, or payment.
