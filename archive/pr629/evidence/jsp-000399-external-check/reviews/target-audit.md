# External-checker pilot: exact submitted target audit

17 September 2026. Read-only proof/source review; this document does not report a Nanoda run. No proof, dependency cache, exporter, or public submission was modified by this audit. The reviewer is an internal Codex collaborator who participated in earlier mathematical research and other packets, not an independent external human reviewer.

## Decision: check the current 27-point packet

The submitted JSP-000399 packet is **`evidence/jsp-000399-parametric-27/`**, not the historical reflection packet. The current local status receipt identifies [PR629](https://github.com/TheJustinSunPrize/awards/pull/629) at head [`86cf6d9a47a7134e9901c6464322eafddc89742e`](https://github.com/Gott-L/awards/tree/86cf6d9a47a7134e9901c6464322eafddc89742e/evidence), with 175 changed files, eight packets, and 48 proof modules. Its [current index](https://github.com/Gott-L/awards/blob/86cf6d9a47a7134e9901c6464322eafddc89742e/evidence/gott-l-formalization-index.md) names the five-parameter 27-form identity and its positive distinct specialization.

`WORK_LOG.md` explicitly records that the earlier reflection branch was not included in the parametric submission. The local presence of `submission/Jsp399.lean`, `submission/Jsp399General.lean`, or `awards/evidence/jsp-000399-reflection/` does not make them part of the current PR. The pilot recommendation in `next-after-eight-verification.md` must therefore be narrowed: checking `JSP399.counterexamples` or `JSP399General.general_half_sum_counterexamples` can be an accurately labelled historical compatibility experiment, but cannot count as checking a current packet endpoint.

The PR identity and remote-blob match above are taken from the root agent's saved `PR629-STATUS.json` and current index; this audit independently inspected and hashed the actual local packet source. It did not repeat the root's complete 175-blob remote audit.

**Recommended stages:**

1. A small compatibility check may use the current module `Jsp399TripleCore`, explicitly selecting `JSP399TwentySeven.triples_complete`, `triples_nodup`, and `triples_length`. These are meaningful submitted enumeration lemmas. A pass covers only those lemmas and their dependencies, not a subset-sum collision theorem.
2. The smallest central identity to select is `JSP399Parametric.vector_triple_sums_perm` from module `Jsp399Parametric`. It proves the full five-dimensional coefficient-spectrum identity. It already requires the large encoded arithmetic certificate; there is no honest small six-point replacement for this stage.
3. For a minimal useful check of the packet's advertised mathematical endpoints, also select `JSP399Parametric.every_translated_parameter_collision` and `JSP399Parametric.example_is_nontrivial_collision`, plus the enumeration lemmas in stage 1. This checks the uniform five-integer-parameter identity with common translation and the actual distinct positive 27-entry example. If reporting the additive-image result too, explicitly select `JSP399Parametric.every_additive_image_collision`.

A successful stage 3 can support a claim about these named endpoints of **one packet**. It cannot support “eight packets independently checked,” “all 48 modules checked by Nanoda,” or official acceptance.

## Source identity and build closure

The current packet's four files match the SHA-256 values in its existing Lean verification receipt:

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `Jsp399TripleCore.lean` | 4,335 | `ec6d0d0bf114c025bbcd5a82a77d3b0401433a2df630438a3f60e602f76b7ee4` |
| `Jsp399Witness.lean` | 1,371 | `4f1937d3fe11b213adb5fe3301e0bb0fd546238063993521fd26ca32da525503` |
| `EncodedCoeffCertificate.lean` | 441,117 | `2d64c4d56c8963a45597d8f933fb71e08b0d8e3f08f7a6ff057c588faaa94f23` |
| `Jsp399Parametric.lean` | 12,153 | `fd486be111060dafac013d577fc75152b4ff1139187f5def7332efd15d832e77` |

The complete project-local import graph is:

```text
Jsp399TripleCore → Std
Jsp399Witness → Jsp399TripleCore
EncodedCoeffCertificate → Jsp399TripleCore
Jsp399Parametric → Jsp399Witness, EncodedCoeffCertificate
```

Use the existing Lean 4.19.0 distribution, copy these exact source bytes into an isolated build directory, replace the project library search path with that fresh directory, and compile in the order above. The packet requires the documented 64 MiB Lean stack setting. Its existing `verify.py` and receipt are same-kernel verification evidence, not evidence of an external checker pass.

Module import closure and exported declaration closure are different. An exporter selecting one theorem need not export every declaration from every imported module. Require and record the actual exported declaration inventory rather than assuming that all public helpers appear automatically.

## Exact theorem and semantic inventory

All names below refer to the submitted files, not locally invented wrappers.

### Enumeration semantics

In `Jsp399TripleCore.lean`, namespace `JSP399TwentySeven`:

- `Index := Fin 27`; `Triple := Index × Index × Index`.
- `indices := List.ofFn (fun i : Index => i)`.
- `tails` and `triples` enumerate the pairs and triples satisfying increasing index order.
- `triples_complete` (line 48): `(i,j,k) ∈ triples ↔ i < j ∧ j < k`.
- `triples_nodup` (line 53): `triples.Nodup`.
- `triples_length` (line 60): `triples.length = 2925`.

These three theorems should be explicit export roots. The collision proofs use the definition `triples`, but need not reference the completeness/nonduplication proofs. A dependency-only export of the collision theorem could therefore omit the very lemmas establishing that its list represents all ordinary three-element index subsets exactly once.

### Parameter-independent identity

In `Jsp399Parametric.lean`, namespace `JSP399Parametric`:

- `Vec := Int × Int × Int × Int × Int`.
- `coefficientVectors` is the explicit list of 27 vectors: zero, the ten signed doubled coordinate vectors, and the sixteen sign vectors with an even number of negative coordinates.
- `vectorA` reads this list; `vectorB` negates each vector through `vneg`.
- `vadd` is coordinatewise integer addition, and `vectorSums a` maps each element of `triples` to the sum of its three entries.
- `vector_triple_sums_perm` (line 169) has exact result `(vectorSums vectorA).Perm (vectorSums vectorB)`.

Its proof depends on `JSP399CoeffCertificate.encoded_triple_sums_perm`; the two `code*_matches` bridges; `encoded_sums`; coordinate bounds; `encodeCoeff_inj`; and `perm_of_map_injOn`. The certificate's private merge-tree declarations are real proof dependencies and must remain in the export, even though their generated names are internal. The base-13 encoding is injective on the proved coordinate range `[-6,6]`; equality of encoded lists is not assumed to imply equality of vectors without this bridge.

The certificate ends at `EncodedCoeffCertificate.lean` line 3568. Its proof uses the computed `encoded_sums_A`, `encoded_sums_B`, and `sorted_encoded_sums_equal` together with proved permutation-preserving merge computations. The private numeric equalities use ordinary kernel checking, including `decide +kernel`; no `native_decide` or compiler-trust axiom is required.

### Uniform scalar endpoint

- `evaluate p v` is the integer dot product.
- `familyA p i := evaluate p (vectorA i)` and `familyB p i := evaluate p (vectorB i)`.
- `integerTripleSums a := triples.map (fun t => a t.1 + a t.2.1 + a t.2.2)`.
- `SameIntegerTripleSums a b := (integerTripleSums a).Perm (integerTripleSums b)`.
- `translated shift a i := shift + a i`.
- `every_translated_parameter_collision` (line 234) quantifies **every** `shift : Int` and `p : Vec`, concluding `SameIntegerTripleSums (translated shift (familyA p)) (translated shift (familyB p))`.

This result allows repeated evaluated entries. It is an indexed-list identity with multiplicities, not a claim that every parameter tuple gives two distinct sets. The intermediate `every_parameter_collision` is a dependency, but should also be an explicit root if its own printed statement is to be advertised. The optional `every_additive_image_collision` (line 177) has the broader type-and-addition interface recorded in the packet; it is not a dependency of the specialized integer endpoint.

### Genuine distinct-set specialization

`exampleParameters := (1,3,9,27,81)`, and `exampleA`, `exampleB` translate the two families by 163. `values a := indices.map a`.

`example_is_nontrivial_collision` (line 283) proves a conjunction of:

1. both value-list lengths equal 27;
2. both lists have `Nodup`;
3. every indexed entry in both is positive;
4. `SameIntegerTripleSums exampleA exampleB`;
5. the two underlying membership predicates are different.

This is the actual nonvacuous counterexample endpoint. It is not merely conditional on distinctness. The explicit completeness/nonduplication roots above make its ordinary-subset interpretation reviewable. To connect the theorem to the two ascending lists printed in the README, additionally export `exampleA_matches` and `exampleB_matches_reverse`. The latter records that `exampleB` uses the reverse order of the displayed natural list `B`; order reversal does not change the represented set. Those display bridges are not automatically required by the main endpoint's proof.

Do not substitute `collision_with_distinct_entries` for the concrete endpoint: that helper accepts `Nodup` hypotheses and alone does not prove positive, different examples exist. Conversely, no separate Mathlib `Finset ℂ` theorem is claimed by this Std-only packet.

## Ensuring that Nanoda checks these exact targets

The pinned checker is [`ammkrn/nanoda_lib@4c544ed4099c8227f07d5de77ad1e69fb0740a27`](https://github.com/ammkrn/nanoda_lib/tree/4c544ed4099c8227f07d5de77ad1e69fb0740a27). The following recommendations come from its actual `main.rs`, `parser.rs`, `tc.rs`, and `util.rs`, read from the pinned local source, not only its README.

- `pp_declars` selects output for inspection; it is **not** a theorem-checking filter. `main.rs` invokes `check_all_declars`, and `tc.rs` checks theorem bodies against their declared types for every exported declaration.
- Explicitly set `unknown_pp_declar_hard_error: true` and place every intended root in `pp_declars`. `parser.rs` lines 402–414 then reject missing names. Do not rely only on a generic success banner or positive declaration count.
- Explicitly permit only `propext`, `Classical.choice`, and `Quot.sound`; set `unpermitted_axiom_hard_error: true` and `unsafe_permit_all_axioms: false`. Do **not** copy the README example's extra `Lean.trustCompiler` allowance. The submitted packet does not need it.
- Set `num_threads: 1`. Enable the natural-number kernel extension if needed for literal computation, disclosing this standard checker option. Keep `string_extension: false` unless a separately reviewed compatibility step establishes the different Lean-version string behavior. Inventory actual `strVal` records; namespace-name strings are not string-literal expressions.
- Reject pretty-printer errors explicitly. `main.rs` can return `Ok(...)` containing a pretty-printer-error message after successful type checking, so exit code zero alone is insufficient for the required statement display.
- Decode the NDJSON name table and require exactly one genuine `thm` record for each root, including its `type` and `value` expression references. Record declaration kind, resolved name, type rendering, and root list, together with full input/configuration/compiler/exporter/checker hashes. A same-name axiom, omitted root, or truncated output is not a pass.
- The exporter's normal theorem branch recursively exports dependencies of both type and proof value. Do not use `--ignore-missing`, `--export-unsafe`, or an export-all fallback that admits unrelated axioms. Retain internal certificate dependencies; removing them to shrink the file would sever the proof.
- Fresh compilation plus byte-matched source establishes the source-to-export provenance. The checker verifies the exported calculus, while human/source review must still establish that the definitions above express the intended subset-sum statement. No checker result alone establishes that semantic correspondence.

## Negative controls and result labels

For each selected mathematical endpoint to which a success claim is attached, retain the successful input unchanged and derive separate controls from it:

1. **Bad proof:** preserve the target name, universe parameters, and type, but replace its proof-value reference with a valid already exported natural-number expression. Require failure from checking the resulting type mismatch. A parse error, missing dependency, absent target, resource timeout, or unrelated pretty-printer failure does not satisfy this control.
2. **Unpermitted axiom:** replace the same target theorem with an axiom of the same name/type, remove its proof field, and keep the allowlist unchanged. Require the checker's explicit unpermitted-axiom error naming that target. Do not allowlist the target to make the control pass.

Record a structured diff showing that each control changes only the intended target declaration, and hash all inputs and logs. An optional absent-target control can separately test the missing-name guard; it does not replace either proof/axiom control.

No target has gained an external-checker pass merely by this audit. If the actual large certificate exceeds the pilot's resource ceiling, stop with a precise result such as “current enumeration lemmas checked; current collision endpoints not completed.” If stage 3 succeeds, the accurate description is that the listed JSP-000399 endpoints and their exported dependency closure were accepted by the pinned independently implemented checker, operated by the same team, with disclosed exporter adaptations and rejected negative controls. The remaining seven packets, independent human review, and official verification remain outside that result.
