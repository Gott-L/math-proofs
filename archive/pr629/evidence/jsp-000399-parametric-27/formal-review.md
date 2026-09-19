# Internal semantic review

Date: 2026-09-17. Scope: the four Lean sources identified below, particularly the transition from the finite encoded certificate to the universal coefficient identity and its concrete positive-integer example.

This is an internal multi-agent review, not an official prize review, an external independent review, or a reviewer signature. The reviewing agent authored `Jsp399TripleCore.lean`, `Jsp399Witness.lean`, and `EncodedCoeffCertificate.lean`. A different agent authored `Jsp399Parametric.lean`; this review examines that module and the integration of the components. A separate internal review examines the shared core. No mathematical-priority or award-eligibility conclusion is made.

## Semantic findings

1. `triples_complete`, `triples_nodup`, and `triples_length` establish that the shared list contains exactly the 2,925 increasing triples of distinct indices from `Fin 27`, once each. Mapping a sum over this list retains equal sums as separate occurrences.
2. The encoded certificate proves `List.Perm`, rather than equality of the supports of the sums. Every generated numerical intermediate is checked by Lean. The merge helpers preserve permutation for every fuel value, including the fallback case; no unproved sorting-correctness or fuel-sufficiency assumption is needed.
3. The literal source codes are connected to the coefficient vectors by `codeA_matches` and `codeB_matches`. The source-digit shift is 2; adding three source codes gives the coefficient-sum encoding with digit shift 6. This explains the offsets 61,882 and 185,646 without assuming a correspondence between unrelated finite examples.
4. Each source coordinate lies in [-2,2], so every triple-sum coordinate lies in [-6,6]. After adding 6, all five base-13 digits lie in [0,12]. `encodeCoeff_inj` proves injectivity on precisely these bounds. `perm_of_map_injOn` then recovers a permutation of the full vectors, including repeated vectors, from the encoded permutation.
5. `every_additive_image_collision` maps this vector permutation through an arbitrary function that preserves `vadd`. Its conclusion uses the same left-associated triple sums, so no unstated algebraic structure on the target is required. Integer evaluation gives all five integer parameters, and a common integer translation adds three times that translation to every sum.
6. Arbitrary parameters may yield repeated values or identical families. The general identity does not claim otherwise. `collision_with_distinct_entries` explicitly assumes distinctness for its finite-set interpretation. `example_is_nontrivial_collision` supplies unconditional length 27, no duplicates, positivity, equality of triple-sum multisets, and different underlying sets for parameters (1,3,9,27,81) and translation 163. The value 44 distinguishes the sets. `exampleA_matches` and `exampleB_matches_reverse` connect both families to the displayed increasing numerical lists.

No unresolved semantic defect was identified in this scope. The result concerns a particular 27-element family and its images; it does not prove the eventual-uniqueness assertion for all sufficiently large cardinalities or classify all exceptional cardinalities.

## Checks and trust boundary

The encoded certificate compiled successfully with Lean 4.19.0. Its two source-list equalities and final numerical equality use no axioms; its permutation endpoint uses `propext`. The reviewer also separately compiled the final parametric module successfully in approximately 3.4 seconds using the existing compiled dependencies. All five printed main endpoints depend only on the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. No additional axiom, `sorry`, `admit`, or native evaluation is part of the proof.

Fresh compilation of every source is assessed separately in the reproducibility receipt. This review does not substitute for that receipt or for external review. Compilation requires Lean's `-s 65536` option for a 64 MiB thread stack; the encoded certificate may take several minutes.

## Reviewed source fingerprints

SHA-256 hashes identify the reviewed versions; a later source change requires reassessing the affected portion of this review.

| Source | SHA-256 |
| --- | --- |
| `Jsp399TripleCore.lean` | `ec6d0d0bf114c025bbcd5a82a77d3b0401433a2df630438a3f60e602f76b7ee4` |
| `Jsp399Witness.lean` | `4f1937d3fe11b213adb5fe3301e0bb0fd546238063993521fd26ca32da525503` |
| `EncodedCoeffCertificate.lean` | `2d64c4d56c8963a45597d8f933fb71e08b0d8e3f08f7a6ff057c588faaa94f23` |
| `Jsp399Parametric.lean` | `fd486be111060dafac013d577fc75152b4ff1139187f5def7332efd15d832e77` |
