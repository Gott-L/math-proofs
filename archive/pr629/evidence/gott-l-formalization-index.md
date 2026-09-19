# Gott-L: nine scoped Lean formalization contributions

This evidence submission gathers nine completed formal results across eight catalogue entries. Each packet preserves its exact theorem, prior-work disclosures, pinned dependencies, fresh verification record and reproduction instructions. The requested assessment concerns the actual formalization contributions. No packet is presented as resolving every formulation of its broader catalogue problem.

## Contributions and exact boundaries

| Catalogue entry | Completed result | Scope remaining outside this packet | Evidence |
| --- | --- | --- | --- |
| JSP-000399 / Erdős 494 | A five-parameter 27-form triple-sum reflection identity and a checked distinct-positive-integer specialization | General eventual reconstruction and first priority for the already formalized fixed existence result | [Proof and checks](jsp-000399-parametric-27/README.md) |
| JSP-000883 / Erdős 1063 | For all n ≥ k ≥ 2, at least one n−i with i<k does not divide choose(n,k), including the exact registered exists_exception variant | Least-starting-point asymptotic bounds are outside this particular packet | [Proof and checks](jsp-000883-exists-exception/README.md) |
| JSP-000737 / Erdős 886 | The complete known infinite four-divisor construction at C=16, and C=9 for the same family, with strict real interval endpoints | The main universal upper-bound question and global optimality of constants | [Proof and checks](jsp-000737-rosenfeld-16-9/README.md) |
| JSP-000295 / Erdős 357 | The complete known infinite-sequence lower-density-zero theorem with the original global distinct-consecutive-sums hypothesis | Full density zero, reciprocal-series convergence and the finite extremal conjecture | [Proof and checks](jsp-000295-lower-density/README.md) |
| JSP-000904 / Erdős 1087 | Exact equal-distance four-point counting identities, the universal planar comparison F≤W≤10F, and an exact four-point example attaining 10 | The original open asymptotic exponent, general isosceles bounds, and the external analytic estimates | [Proof and checks](jsp-000904-distance-counting/README.md) |
| JSP-000883 / Erdős 1063, additional endpoint | For every ε>0, eventually an actual unique-exception witness satisfies n≤exp(εk); the actual minimum has log(n_k)=o(k) and log(n_k)/k→0 | Sharp growth order, exact values, mathematical discovery, and priority for the improved-upper target already formalized in PR601 | [Proof and checks](jsp-000883-subexponential/README.md) |
| JSP-000847 / Erdős 1017 | Complete classical Erdős–Goodman–Pósa theorem: every finite simple graph has an exact edge partition into at most floor(n²/4) edges and triangles, including empty graphs and isolated vertices | The open dense-graph improvement, mathematical discovery, global first priority and award eligibility | [Proof and checks](jsp-000847-egp-partition/README.md) |
| JSP-000791 / Erdős 951 | Every finite strictly increasing prefix above one with complete exponent-vector product separation extends to an infinite sequence preserving that prefix and separation; valid new generators exist above every cutoff | The original eventual prime-counting conjecture, near-optimal numerical certificates, mathematical discovery, global first priority and award eligibility | [Proof and checks](jsp-000791-prefix-extension/README.md) |
| JSP-000279 / Erdős 336 | Complete classical Erdős–Graham characterization: a bounded-summand asymptotic basis has a least fixed exact order iff its differences have gcd one, including the strictly increasing sequence/consecutive-difference version | The extremal-limit question, optimal quantitative order bounds, mathematical discovery, global first priority and award eligibility | [Proof and checks](jsp-000279-exact-order-criterion/README.md) |

The 174 file blobs in the first eight evidence packets remain unchanged. The ninth mathematical packet adds 24 files. A separate 45-file external-checker supplement strengthens verification of the existing JSP-000399 packet and is not counted as another mathematical contribution. Each mathematical package is reproducible separately. No catalogue, candidate, award, recipient-confirmation or payment record is changed.

## Review request and prior work

Please assess these formalization contributions under the [official selection rules](https://www.hejustinsun.com/prize/rules), including the community-contribution and partial-progress provisions where applicable. The request does not presume a tier, eligibility decision, first-priority finding, or payment allocation. Repository publication and local checks do not substitute for official verification and adjudication.

The related submissions, original mathematical authors and reused code are identified in each packet. The bounded source searches distinguish these particular endpoints from prior examples or other variants; they are not global priority certificates. The fixed 27-element existence result already has a public Lean proof; the C64 precursor to the four-divisor construction retains its MIT notice; and the fifth packet formalizes the credited finite-counting argument in [haipapa123's PR586](https://github.com/TheJustinSunPrize/awards/pull/586).

For the sixth packet, the subexponential mathematics is already public in Patrick White's and Ricky Cipollini's related work. [56647563's PR601](https://github.com/TheJustinSunPrize/awards/pull/601) already formalizes the improved-upper target at a fixed positive exponential rate. Its licensed finite proof is explicitly reused and credited. The additional formalization extends the parameter to an arbitrary root degree chosen after ε, proving the stronger quantified subexponential endpoint. Source-access limits and reuse are disclosed in that packet.

For the seventh packet, the mathematical theorem is credited to Erdős, Goodman and Pósa (1966). The inspected PR600 proves sharpness but explicitly excludes the universal upper bound; the other inspected same-name artifacts do not close that theorem. The new proof constructs the entire partition and discharges its matching and induction premises. Its bounded source search is not a global priority certificate. The catalogue’s “Eligible to claim: No” field is preserved, and this request concerns assessment of the formalization contribution.

For the eighth packet, the known finite-prefix extension argument is credited to Barreto–Price and Patrick White with Claude, with the source-access limits stated in the packet. The new implementation uses summable geometric weights and outer-measure bounds to construct a valid next generator, then iterates while preserving every old coordinate. The complete exponent-vector separation condition is retained. PR670's different three-generator lower bound is credited but its code is not reused. The catalogue's eligibility field is unchanged.

For the ninth packet, the mathematical characterization is credited to Erdős and Graham (1980). The proof derives actual finite equal-sum representations of adjacent lengths from the full common-divisor condition, then proves uniform padding and least-order existence. It includes both directions and the original sequence formulation. The distinct example in PR660 and the extensive plby E336 extremal-limit development are explicitly acknowledged; no source code from them is reused. The catalogue's eligibility field is unchanged. See [sources and scope](jsp-000279-exact-order-criterion/SOURCES.md).

## Verification

The nine mathematical packets contain fifty-three proof modules. Their recorded fresh compilations and per-packet axiom audits all passed: respectively 18, 10, 28, 20, 54, 86, 25, 38 and 34 named declaration checks. Only standard logical axioms are permitted. Each package records its own exact statement checks and source hashes; eight packages use the pinned Mathlib 4.19 dependency cache and the first uses bundled Std.

The fifth packet also passed a separate fresh replay by a same-team agent that did not write its seven proof modules: fifteen independently transcribed statements and 93 named audits. Its T is explicitly encoded as unordered pairs of equal edges sharing a unique vertex.

The sixth packet passed ten primary statement checks and a separate fresh replay of all eleven modules, twelve independently transcribed statements and 98 named audits. Its reviewer ported the inherited finite modules but did not write the new prime-count, parameter, asymptotic or minimum proofs. The checks verify actual witnesses, nonemptiness, the literal natural infimum and the order of quantifiers in the subexponential conclusion.

The seventh packet passed fresh compilation of seven modules, 25 named declaration audits and four explicit statement checks. A separate internal replay passed eight independently transcribed statement checks and 33 audits, including the complete endpoint for arbitrary finite simple graphs and unique ownership of every edge; details are recorded in [its review receipt](jsp-000847-egp-partition/review-a/receipt.json). Its reviewer authored the matching module and reviewed the other components. No assumed partition or matching remains in the final theorem.

The eighth packet passed fresh compilation of seven modules, 38 selected named declaration audits and six explicit statement checks. Its separate internal replay passed 12 independently transcribed statements and 51 audits, including one additional named source helper already present in the main endpoints' dependency closure. Its reviewer authored the append and sequence modules; the other five modules were written by other agents. The checks include product injectivity, finite-support equality, unconditional avoidance and extension, and the empty-prefix and zero-vector cases.

The ninth packet passed fresh compilation of five modules, all 34 named public declaration audits and eight explicit statement/edge-case checks. A separate internal replay passed 12 independently transcribed checks and 46 audits (34 source declarations plus 12 review declarations), with all nine dependency revisions and tracked-source cleanliness checked. Its reviewer authored the definitions, padding and necessity modules and reviewed the other two modules. An additional same-team non-author mathematical review found no weakened premise or missing finite-certificate argument. Both reviewer roles and dependency-cache trust are disclosed.

Internal reviews disclose the reviewers' participation in development. They are not official verification, independent human review, or separate implementations of the Lean kernel. Pinned dependency-cache trust is disclosed. Earlier packets' sources and internal evidence remain unchanged.

## Separately implemented checker: JSP-000399

The [external-checker supplement](jsp-000399-external-check/README.md) records an actual successful Nanoda run for ten explicit endpoints and semantic bridges of the unchanged five-parameter packet, accepting 2,882 declarations. These include the complete coefficient identity, uniform parameter and translation results, the positive distinct example, enumeration completeness/nonduplication, and displayed-example bridges.

The checker source was unmodified at `ammkrn/nanoda_lib@4c544ed4099c8227f07d5de77ad1e69fb0740a27`. The exporter was explicitly adapted to Lean 4.19 and seven string literals were expanded into kernel-checked ordinary constructors. Its changes, source hashes, exact input/binary hashes, statements, successful logs, and both deliberately invalid controls are included. The wrong-proof and unpermitted-axiom controls both target `JSP399Parametric.vector_triple_sums_perm` and failed for their expected reasons.

This is an independent checker implementation operated by the same team. It checks this one mathematical packet, not the other eight; it is not independent human review or official verification. The new optional native-host replay convenience wrapper is marked as prepared but not run end-to-end; the successful evidence comes from the archived actual operator scripts and records.

## Attribution

Gott-L proposed and initiated the project, set the objectives, planning and research direction, and authorizes this submission. OpenAI Codex provided candidate research, proof reconstruction and extension, formal implementation, documentation and internal checks under Gott-L's instructions. Historical mathematical discoveries and prior formalizations retain their named attribution. Project planning is not presented as authorship of earlier mathematical discoveries.

## Immutable packet history

- JSP-000399: [dfedecd53e4daa41151a35692b90d98defe3a8d6](https://github.com/Gott-L/awards/commit/dfedecd53e4daa41151a35692b90d98defe3a8d6).
- JSP-000883, universal nondivisor: [02751f6f848b4536c87cba551f69635c36013f47](https://github.com/Gott-L/awards/commit/02751f6f848b4536c87cba551f69635c36013f47).
- JSP-000737: [0f5b94d8c3d5b00c21ce1ffb8a8a87c886e6687f](https://github.com/Gott-L/awards/commit/0f5b94d8c3d5b00c21ce1ffb8a8a87c886e6687f).
- JSP-000295: [315bc08f5706630f025410330c3ce66ec27acd82](https://github.com/Gott-L/awards/commit/315bc08f5706630f025410330c3ce66ec27acd82).
- JSP-000904: [b21109ece19bcc8b18b9646567dfc6d5ac088d21](https://github.com/Gott-L/awards/commit/b21109ece19bcc8b18b9646567dfc6d5ac088d21).
- JSP-000883, subexponential upper bound: [0bf84f8331887182b61c878f782072ec6d755db2](https://github.com/Gott-L/awards/commit/0bf84f8331887182b61c878f782072ec6d755db2).
- JSP-000847, complete EGP edge partition: [d403cf24e4278a0ec7ed2a4a4698363772a2fcf7](https://github.com/Gott-L/awards/commit/d403cf24e4278a0ec7ed2a4a4698363772a2fcf7).
- JSP-000791, complete finite-prefix extension: [1d0ab6b38db675f827ba5b7bc9f503800ddee5b0](https://github.com/Gott-L/awards/commit/1d0ab6b38db675f827ba5b7bc9f503800ddee5b0).

- JSP-000279, complete exact-order criterion: [0f09fd66cea993c12bb2e61225d32ff8348f518e](https://github.com/Gott-L/awards/commit/0f09fd66cea993c12bb2e61225d32ff8348f518e).
- Verification supplement for existing JSP-000399 (not a new mathematical packet): [f10b19b88dcaf7187eb3a27fd4727e3324233ff2](https://github.com/Gott-L/awards/commit/f10b19b88dcaf7187eb3a27fd4727e3324233ff2).

The individual commits remain available for separate review if the maintainers prefer that organization. This index is licensed CC BY 4.0; packet-specific licenses and notices remain unchanged. Private contact, identity and payment details are excluded.
