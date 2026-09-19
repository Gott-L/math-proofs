# JSP-000399: a five-parameter triple-sum identity and a 27-element certificate

This evidence packet concerns the exceptional cardinality `n = 27`, subset size `k = 3`, in [JSP-000399](https://github.com/TheJustinSunPrize/awards/blob/main/problems/catalog-0301-0400.md#JSP-000399) / [Erdős problem 494](https://www.erdosproblems.com/494). It supplies an independently written Lean implementation of a parameter-independent coefficient identity and a concrete pair of different sets of 27 distinct positive integers with identical three-element-subset-sum multisets.

**A prior Lean certificate for the existence of a distinct 27-element counterexample is already public.** [Formal Conjectures issue 5655](https://github.com/google-deepmind/formal-conjectures/issues/5655), opened on 11 September 2026, links an [automated audit with a fixed-witness Lean proof](https://tadamcz.com/fc-review-results/c90271f0fa/files/ErdosProblems/494.json). The audit reports successful compilation and no placeholder proofs; we do not represent that report as our own reproduction of its toolchain. Our concrete witnesses differ, but that does not establish priority for the existence theorem. We make no first-formalization claim for that theorem, and ask that any contribution be assessed at its actual scope.

## The parameter identity

Let `r = (r₁,r₂,r₃,r₄,r₅)` be any five integers. Form a **27-entry indexed list**, comprising:

- the entry `0`;
- the ten entries `±2rᵢ`, for `1 ≤ i ≤ 5`;
- the sixteen entries `ε₁r₁ + ··· + ε₅r₅`, where each `εᵢ` is `±1` and the product of the five signs is `+1`.

Let the second list be the entrywise negative of the first. The two lists have equal multisets of sums of three **distinct indices**. This assertion is uniform in all five parameters. Collisions between values are allowed in this general statement; when the entries are distinct, the index subsets are exactly the ordinary subsets of the represented set.

The proof starts with the 27 corresponding coefficient vectors in `ℤ⁵`. The complete multiset of their 2925 triple sums agrees with that of the negated vectors. Linear evaluation against any parameter vector preserves vector addition and transports that multiset equality to the claimed scalar identity. This proves all parameters at once, rather than inferring a universal theorem from numerical samples.

The [review note](independent-review.md) also gives an elementary Laurent-polynomial explanation of the identity. Neither that explanation nor any Lie-theoretic interpretation is an assumption in the Lean certificate.

## A pair of actual sets

Choose `r = (1,3,9,27,81)` and translate both lists by 163. The increasing rearrangements are:

```text
A = [1,44,48,60,68,96,104,109,116,120,145,157,161,163,
     165,169,181,204,212,217,224,228,260,264,276,284,325]
B = [1,42,50,62,66,98,102,109,114,122,145,157,161,163,
     165,169,181,206,210,217,222,230,258,266,278,282,325]
```

Each contains 27 distinct positive integers. They are different as sets: 44 occurs only in `A`. Both have total sum 4401. Their 2925 triple sums have the same multiplicities, with 563 different values between 93 and 885. The largest multiplicity is 45, at sum 489.

The concrete endpoint proves positivity, no repeated entries, both lengths, inequality of the underlying sets, and equality of the full triple-sum multisets. It obtains the last property by specializing the parameter theorem. The shared enumeration proves that all increasing index triples occur exactly once. A proved merge-permutation theorem and a checked injective encoding establish the coefficient identity, preserving repeated values. There is no substitution of equality of attainable values for equality with multiplicities.

## Scope and credit

The concrete cardinality 27 is different from the classical half-size case `n = 2k`. An earlier independently written [reflection packet in the submitter's fork](https://github.com/Gott-L/awards/blob/5fc03b5451682bc0be671ccb124d7c05f80f3b5a/evidence/jsp-000399-reflection/README.md) treats that separate case and prominently credits its prior general Lean proof. Neither packet proves the sufficiently-large-cardinality uniqueness theorem of Gordon, Fraenkel, and Straus.

The contribution offered here is the independently written coefficient-vector certificate, its transport to arbitrary five integer parameters, the concrete positive-integer certificate, and reproducible verification records. This description does not assert that the parameter family is mathematically new, that no prior formalization of it exists, or that the work qualifies for a prize. Those are separate attribution and eligibility questions for substantive review.

## Formal statements and verification

| File | Checked content |
| --- | --- |
| [Jsp399TripleCore.lean](Jsp399TripleCore.lean) | Completeness, nonduplication, and cardinality of the increasing index triples; permutation preservation of the recursive merge computation. |
| [Jsp399Witness.lean](Jsp399Witness.lean) | The two displayed increasing positive lists and their different underlying sets. |
| [EncodedCoeffCertificate.lean](EncodedCoeffCertificate.lean) | Explicit finite arithmetic certificate for the encoded coefficient sums, with every intermediate equality checked in Lean's kernel. |
| [Jsp399Parametric.lean](Jsp399Parametric.lean) | Bounds and injectivity of the encoding, reflection of multiset equality, arbitrary additive images, all five integer parameters and translations, and the concrete distinct positive example. |

The main declarations are `vector_triple_sums_perm`, `every_additive_image_collision`, `every_parameter_collision`, `every_translated_parameter_collision`, and `example_is_nontrivial_collision` in namespace `JSP399Parametric`. The last includes both lengths, both `Nodup` properties, positivity, full triple-sum multiset equality, and inequality of the underlying membership predicates. `exampleA_matches` and `exampleB_matches_reverse` connect the specialization to the displayed numerical lists.

The coefficient sums lie in `[-6,6]` in each of five coordinates. Adding six produces radix-13 digits, so the code is injective on every possible sum. That injectivity is proved, not inferred from testing. A separate list lemma reflects a permutation of the encoded lists back to a permutation of the original vectors, including repetitions. The certificate's merge lemma preserves permutations for every fuel value; no unproved sortedness assumption is needed.

The additive-image theorem quantifies over any type with addition and any map preserving vector addition. It can be instantiated in richer external libraries, but this packet does not include a separate Mathlib `Finset ℂ` theorem. Its set interpretation uses complete index enumeration and distinct entries, as described above.

To reproduce with **Lean 4.19.0** and Python's standard library, run from this directory:

```text
python verify.py --lean lean --receipt verification.json
```

An explicit path to the pinned Lean compiler may replace `lean`. The [script](verify.py) copies all four sources into a fresh temporary directory, replaces the local library search path, compiles in dependency order, treats warnings as errors, and verifies all eighteen named axiom reports. It supplies `-s 65536` (64 MiB per-thread stack), which is required for the large finite checks on the tested Windows toolchain. A default-stack compilation can fail before checking the certificate. Allow several minutes and several GiB of RAM for the encoded certificate.

The [receipt](verification.json) identifies each source by SHA-256 and byte count and records actual compiler output. Audited dependencies are confined to Lean's standard `propext`, `Classical.choice`, and `Quot.sound`; some arithmetic certificates have no axiom dependencies. The sources use no placeholder proofs, custom axioms, `native_decide`, or `unsafe` declarations. Only Lean's bundled standard library is required. The [Lake configuration](lakefile.toml) and [toolchain pin](lean-toolchain) also support `lake build` with the required stack setting; the recorded complete reproduction is the fresh-directory script run.

The [arithmetic and algebraic review](independent-review.md) and [formal statement review](formal-review.md) distinguish each reviewer's authored components from components they separately checked. All checks use the same Lean distribution and kernel. No independently implemented kernel check, independent external archive, or official reviewer signature is asserted.

## Background references

- D. V. Fomin, [*Is the Multiset of n Integers Uniquely Determined by the Multiset of Its s-sums?*](https://arxiv.org/abs/1709.06046), surveys the reconstruction problem and exceptional-cardinality literature. General multiset examples with repeated entries do not by themselves prove a distinct-set result.
- R. Slansky, [*Group theory for unified model building*](https://www.iitg.ac.in/cet/gian/2017/ppoulose/gian_ksb/Slansky_GT.pdf), Physics Reports 79 (1981), Table 15, printed p. 88, gives the familiar `1 + 10 + 16` representation pattern that suggested the construction.
- Stephen J. Haris, [*Complete reducibility of admissible representations over function fields*](https://msp.org/pjm/1978/79-2/pjm-v79-n2-p12-s.pdf), Pacific J. Math. 79(2) (1978), printed p. 491, describes the signed half-spin weights. These representation-theoretic references explain the structural inspiration; the triple-sum identity itself is established by the self-contained certificate.

## Contributions

- **Gott-L:** project concept and initiation, overall objectives and research direction, and authorization and ownership of the submission.
- **OpenAI Codex, working under Gott-L's instructions:** candidate research, construction of the displayed witnesses, Lean implementation, documentation, and computational and formal cross-checks.
- **Prior mathematical and formalization authors:** credited in the linked sources; project leadership is not a claim of priority for their results.

Internal sibling-agent reviews use the same assistant and tool environment and are not independent human peer review or official prize verification. Code is licensed under [MIT](LICENSE); prose and verification records are under [CC BY 4.0](LICENSE-CONTENT). No third-party proof source is incorporated.
