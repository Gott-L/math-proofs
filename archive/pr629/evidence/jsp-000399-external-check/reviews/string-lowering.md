# Lean 4.19 string lowering: internal review and checker handoff

17 September 2026. This review covers the actual seven string literals in the current JSP-000399 27-point packet's exported dependency closure. It does not establish general compatibility between Lean versions. The reviewer did not author the exporter adaptation, but wrote the checker runner and participated in the project's mathematical research. This is internal source review and a separately implemented checker operated by the same team, not independent human review or official verification.

## Reviewed adaptation

The inspected adapted `exporter/Export.lean` has SHA-256 `070dd8c3abd862c2ac3b99cd9e69719e098e05fc0cd22540fc7a62ceda481e4b`. Its separate `string-lowering.patch` has SHA-256 `38bbba084b98542ddf1c9e084f5f2998d4dd1c83236208b4d65006f965b341ed`.

`lowerStringLiteral` traverses `s.toList` in its original order using a right fold. It constructs `List.nil.{0} Char`, adds each character with `List.cons.{0} Char (Char.ofNat c.toNat)`, and applies `String.mk` to the resulting list. The implementation uses Lean 4.19's `mkNatLit`; that is the frontend `OfNat.ofNat Nat n (instOfNatNat n)` expression, not a raw natural-number literal. This distinction matters for exact syntax comparison, although the two representations are definitionally equal.

The transformation is applied recursively through application, lambda, forall, let, and projection expressions before expression interning. Parent expressions are therefore interned in the same normalized form as their children. The existing let optimization-flag normalization is preserved. The exporter explicitly visits constants introduced by the normalized expression and exports their definitions. A residual string literal triggers an error; it is not dropped or replaced by a proof assumption. The exporter's metadata identifies the modified string-lowering implementation.

No Nanoda code was changed. The checker runs with its string extension disabled and checks the resulting ordinary constructor expressions. Its natural-number extension remains enabled, and only `propext`, `Classical.choice`, and `Quot.sound` are permitted axioms.

## Independent checks of the actual literals

The original full export has SHA-256 `bf9c742f6def570ef5ccb51e6886d712e2d97db9bac21806d329a4f6537bafd5`. It contains exactly these seven literal strings, all ASCII:

```text
"PANIC at "
" "
":"
": "
"Init.GetElem"
"_private.Init.GetElem.0.List.get!Internal"
"invalid index"
```

The independent script [review_literals.py](review_literals.py) extracts those records directly from the original export and generates [ActualLiterals.lean](ActualLiterals.lean). Each theorem states that the original string equals an explicit `String.mk` list of numeric `Char.ofNat` expressions, and proves the equality with `rfl`. This source imports only bundled `Std`, not the modified exporter.

All seven equalities compiled under the original Lean 4.19.0 binary with `--trust=0` and warnings treated as errors. Each reported no axiom dependencies. The exact compiler, source, input, output and driver hashes are in [literal-kernel-result.json](literal-kernel-result.json). This establishes the definitional equalities for the actual replacement cases; it does not claim arbitrary Unicode or other-version support.

A separate structural audit, [compare_exports.py](compare_exports.py), canonicalizes name, level and expression references and compares the original export with the lowered export. It applies only the reviewed seven string expansions to the original expression DAG. The final [structural-comparison.json](structural-comparison.json) records:

- 2,882 declarations on each side, with no missing or extra names;
- identical declaration kinds, universe parameters, declared types, definition/proof values and recursor rule right-hand sides after that expansion;
- every expected expanded literal present in the lowered DAG;
- seven original string-literal records and zero remaining literal records.

An initial version of this comparison reported differences in two panic-message definition bodies because it modeled `mkNatLit` as a raw literal. Inspection of the pinned Lean source, `Lean/Expr.lean:726`, identified that comparator error. Matching the actual frontend constructor resolved both differences; the exporter and mathematical proof were unchanged. This audit is a structural consistency check, not a proof that the exporter or checker implementation is correct.

## Actual current-packet result

The lowered export has SHA-256 `43ccad2ef5605b915c0decce923d46245e6da876aed2058ddc603b0ec285a839`, size 10,385,356 bytes. Its export receipt records all ten genuine theorem roots and the unchanged current submitted source hashes. The unchanged Nanoda binary has SHA-256 `bd60ccdb0f08f6a1115975c135ec4117dee3a4ff4daab9278f8e9e0d75871d2e`, built from commit `4c544ed4099c8227f07d5de77ad1e69fb0740a27`.

[The full runner receipt](../results/full-lowered.result.json) records an actual successful run: **2,882 declarations checked, exit 0**, in 31.047 seconds. Exact theorem names and their statements were printed and independently matched against the export's type/value records. The roots are:

```text
JSP399TwentySeven.triples_complete
JSP399TwentySeven.triples_nodup
JSP399TwentySeven.triples_length
JSP399Parametric.vector_triple_sums_perm
JSP399Parametric.every_additive_image_collision
JSP399Parametric.every_parameter_collision
JSP399Parametric.every_translated_parameter_collision
JSP399Parametric.example_is_nontrivial_collision
JSP399Parametric.exampleA_matches
JSP399Parametric.exampleB_matches_reverse
```

Both targeted negative controls preserved the name, type and universe parameters of `JSP399Parametric.vector_triple_sums_perm`:

- Substituting an existing natural-number expression for its proof produced exit 101 and the expected definitional-type-equality assertion failure, in 29.922 seconds.
- Replacing that theorem with an unpermitted axiom produced exit 1 and an error explicitly naming the forbidden axiom, in 0.438 seconds.

The successful input was retained unchanged. Separate mutated inputs, exact changed records, configurations and log hashes are recorded. These are two controls on the named coefficient-identity target; the other nine roots were checked but were not individually mutated.

The earlier current-packet enumeration stage also passed: 774 declarations and three enumeration roots, with its two controls, as recorded in [core.result.json](../results/core.result.json). The earlier synthetic run is separately labelled and is not counted as checking a submitted theorem. A first synthetic attempt failed before checking because the pinned checker requires its pretty-printer destination file to exist; the runner was corrected to create a fresh empty output file, and that failed receipt is retained.

The full run measured cumulative tracked storage, including the explicitly accounted 1,868,360,225-byte shared environment, at 2,736,864,885 bytes before and 2,757,646,118 bytes after, below the 3 GiB ceiling. The input was below the runner's 100 MiB negative-control copy limit. Every invocation had a 600-second timeout and one checker thread.

## Scope

The result covers the listed current JSP-000399 endpoints and their exported dependency closure in **one** submitted packet. It includes the complete increasing-triple enumeration, the uniform coefficient/additive/integer/translation identities, the positive distinct 27-entry specialization, and its connection to the printed numerical lists. It does not report a check of all eight submitted packets, all 48 modules, or the historical six-point reflection packet. It neither establishes mathematical discovery/priority nor substitutes for official review or an award decision.

Original review prose is CC BY 4.0. The independent helper scripts and Lean literal-check source in this review are MIT; external sources retain their existing notices and licenses.
