# Sources and bounded prior-work review

Reviewed 17 September 2026. This records specific inspected sources, not a
global first-formalization certificate.

- P. Erdős and R. L. Graham, *On bases with an exact order*, Acta Arithmetica
  37 (1980), 201–207, Theorem 1 on pp.202–203.
  [Author-archive PDF](https://www.renyi.hu/~p_erdos/1980-22.pdf).
  The original theorem and proof were read. This is the mathematical source
  for the characterization and adjacent-length padding argument. No code or
  extended text from the paper is copied.
- Q.-H. Yang and F.-J. Chen, *On bases with a T-order*, Integers 11 (2011), A5.
  [Journal PDF](https://math.colgate.edu/~integers/l5/l5.pdf).
  The introduction confirms the criterion and Lemma 4 describes the related
  finite equal-sum construction. Its broader T-order result is outside this packet.
- [Official PR660](https://github.com/TheJustinSunPrize/awards/pull/660), pinned
  to `CollinYuanjieRen/awards@72be7ec71c44c6ede324331a428c9ea2bf6ba21b`.
  The complete [Main.lean](https://github.com/CollinYuanjieRen/awards/blob/72be7ec71c44c6ede324331a428c9ea2bf6ba21b/submissions/jsp-000279-cyr/Erdos336OrderExample/Main.lean)
  proves a concrete basis of variable order two and exact order three; its
  scope explicitly excludes the general characterization. Its code is not reused.
- [`plby/lean-proofs` E336 directory](https://github.com/plby/lean-proofs/tree/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos336),
  pinned to `8822f7ddef30fadbd92e1c6ab4ed897af356af5e`.
  All 193 Lean files in that directory (1,052,220 bytes) were obtained and
  searched; the relevant basic, normalization, order-recovery and final modules
  were read. `Admissible r k` already includes `HasExactOrder A k`; the inspected
  weak-to-strong finite-group bridges also assume an exact covering power.
  `Problem336Solution.lean` asserts the extremal limit value `1/3`. This review
  did not rebuild or certify that Lean 4.33 development, and does not present
  the existence criterion here as a substitute for its different endpoint.
  No source code from it is reused.
- [`rjwalters/lean-genius`, Erdos336Problem.lean](https://github.com/rjwalters/lean-genius/blob/dc62f771ed5010abfdb04247dff6143e0e69d3e7/proofs/Proofs/Erdos336Problem.lean),
  pinned to `dc62f771ed5010abfdb04247dff6143e0e69d3e7`.
  The entire file was read. The consecutive-difference characterization
  appears in explanatory prose, not as a proved theorem. Its finset-based
  representation definition forbids repetition and is not used here.
- [Formal Conjectures issue496](https://github.com/google-deepmind/formal-conjectures/issues/496)
  concerns the extremal-limit statement. The direct current `ErdosProblems/336.lean`
  lookup returned 404 in this review. No verified upstream gcd-criterion
  definition is claimed to be copied verbatim; the packet exposes list sums
  and universal divisibility directly.
- Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`, Apache-2.0. The included
  manifest records its dependencies and exact revisions. Existing library
  authors retain their attribution.

The official catalogue entry JSP-000279 records `Progress`, `Lean proof: No`,
`Eligible to claim: No` at the inspected base. This packet asks for assessment
of a scoped formalization contribution and does not alter those fields.
Search indexing, private sources, alternate names and later submissions may
limit any novelty assessment. No discovery, global-priority, official-acceptance
or payment claim is made.
