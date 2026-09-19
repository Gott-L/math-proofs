# Erdős 357: final source-level overlap review

Review date: 17 September 2026. This supplements the initial candidate screening. The reviewer is another agent in the same Codex session and authored the new interval and dyadic-bound modules; this is not organizer-appointed independent verification. No existing proof environment was recompiled, and no globally first formalization or prize eligibility is asserted.

## Conclusion

The actual problem-specific Lean sources linked by prize PR377 and Formal Conjectures PR4918/4967 do **not** contain a proof of the general impossibility of a linear bound for an infinite sequence with distinct consecutive sums, nor a proof of `Erdos357.erdos_357.variants.infinite_set_lower_density`. Their imported copies of that lower-density declaration still end in `sorry`.

This conclusion comes from reading the full relevant proof sources and checking their imports, rather than relying on README descriptions or PR titles. The substantive earlier work is a family of finite constructions and lower bounds on the finite extremal functions. It remains earlier related work and should be credited as such.

## Prize PR377: entire custom proof-module closure read

[PR377](https://github.com/TheJustinSunPrize/awards/pull/377) adds its package at commit `9526fbcdd4a6a7b06c4c85d7e7ef73d45b799056`. The complete GitHub changed-file list contains only these three proof/audit modules, plus `lakefile.lean` as build configuration:

| Complete file read | Lines | Actual contents |
|---|---:|---|
| [JSP000295.lean](https://github.com/ketianzhang1-lang/awards/blob/9526fbcdd4a6a7b06c4c85d7e7ef73d45b799056/docs/submissions/jsp-000295-kz/JSP000295.lean) | 245 | Explicit finite sequence, uniqueness of its block sums, square-root lower bounds, and the Weisenberg asymptotic endpoint. |
| [Compatibility.lean](https://github.com/ketianzhang1-lang/awards/blob/9526fbcdd4a6a7b06c4c85d7e7ef73d45b799056/docs/submissions/jsp-000295-kz/Compatibility.lean) | 26 | Extracted upstream definitions `HasDistinctSums`, `f`, and wrappers for `weisenberg` and `explicit_lower_bound`. |
| [Audit.lean](https://github.com/ketianzhang1-lang/awards/blob/9526fbcdd4a6a7b06c4c85d7e7ef73d45b799056/docs/submissions/jsp-000295-kz/Audit.lean) | 20 | Printed types/axioms and one example invoking the finite lower bound. |

`Audit` imports `JSP000295` and `Compatibility`; `Compatibility` imports `JSP000295`. The latter imports only Mathlib modules. Thus the complete custom mathematical source closure for this package has been read. The nine-line `lakefile.lean` was also inspected in the full added-file patch and names exactly those three roots. It requires Mathlib v4.34.0; the manifest pins Mathlib to `5ed2965256430c3649e86755f9576b54eca72435`.

The argument constructs `entry t i = t²+1+i` on `Fin (2*t+1)`. The lemma `blocks_injective` at line 70 is specific to that sequence and to endpoints bounded by `2*t+1`; it is not a theorem excluding linear growth for arbitrary infinite sequences. `admissible_length_le` at line 177 says a finite strictly increasing sequence in `[1,n]` has length at most `n`. It does not assert any superlinear growth or density-zero property. The final assertions are:

- `lower_bound`: `2*n.sqrt-1 ≤ f n` for all `n`;
- `real_lower_bound`: `2*Real.sqrt n-3 ≤ f n`;
- `weisenberg`: the corresponding lower asymptotic estimate.

No proof in these files has an arbitrary infinite sequence `A : ℕ → ℕ` as an input. There is no density definition, liminf argument, dyadic layer count, or general `no_linear_bound` theorem. Each finite construction is a separately chosen sequence; it does not supply a universal restriction on infinite sequences.

## Formal Conjectures PR4918: full linked proof and its problem import read

The actual [PR4918 patch](https://github.com/google-deepmind/formal-conjectures/pull/4918/files) links [Erdos357BigOLowerBoundFC.lean](https://github.com/KitaKen1/erdos-357-sqrt-lower-bound/blob/d40ef76f3af54a644aeb38e68acd15f667994903/lean/Erdos357BigOLowerBoundFC.lean) at commit `d40ef76f3af54a644aeb38e68acd15f667994903`. All **227 lines** of that source were read.

The file imports only `FormalConjectures.ErdosProblems.«357»`. Its [manifest](https://github.com/KitaKen1/erdos-357-sqrt-lower-bound/blob/d40ef76f3af54a644aeb38e68acd15f667994903/lean/lake-manifest.json) pins Formal Conjectures to `8adf5b7d199d83d7c69d2f89d0e7327362ead98a`, and Mathlib to `a3a10db0e9d66acbebf76c5e6a135066525ac900`.

The proof constructs `tailSequence n` on `Fin n.sqrt`, establishes that its consecutive sums are distinct, proves `sqrt_le_f`, then derives `sqrt_isBigO_f` and the external endpoint `Erdos357.erdos_357.parts.ii.bigO_version_solved`. The interval lemmas work on finite `Fin k` index sets. There is no arbitrary-infinite-sequence impossibility theorem or density-zero argument.

The entire pinned [upstream 357.lean](https://github.com/google-deepmind/formal-conjectures/blob/8adf5b7d199d83d7c69d2f89d0e7327362ead98a/FormalConjectures/ErdosProblems/357.lean) was also read. It contains the lower-density statement with its body `by sorry`; importing that name is not a completed proof of it. The new finite construction does not invoke the lower-density statement.

## Formal Conjectures PR4967: full linked proof and its problem import read

The actual [PR4967 patch](https://github.com/google-deepmind/formal-conjectures/pull/4967/files) links [Erdos357AdditionalTargetsFC.lean](https://github.com/KitaKen1/erdos-357-additional-targets/blob/b60766de669af22303446a7d16563d7b7680ae7e/lean/Erdos357AdditionalTargetsFC.lean) at commit `b60766de669af22303446a7d16563d7b7680ae7e`. All **299 lines** of that source were read.

The file imports the upstream problem, `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`, and `Mathlib.Order.Interval.Set.OrdConnected`. It contains the same finite tail-sequence construction directly, rather than importing a hidden separate local proof module. Its [manifest](https://github.com/KitaKen1/erdos-357-additional-targets/blob/b60766de669af22303446a7d16563d7b7680ae7e/lean/lake-manifest.json) pins Formal Conjectures to `2411d22e1bd550d050d0eac6c1fb379a76a3e7c5` and Mathlib to the same `a3a10db0e9d66acbebf76c5e6a135066525ac900` revision.

After the finite lower construction, the additional lemmas prove:

- distinct singleton sums imply injectivity for `a : Fin k → ℤ`;
- monotonicity plus that injectivity implies strict monotonicity;
- the finite extremal functions satisfy `h(n)=f(n)`;
- `log n=o(sqrt n)`, followed by three lower-growth endpoints for `f` and `h`.

None gives the general infinite `no_linear_bound` or lower-density endpoint. The pinned [upstream 357.lean](https://github.com/google-deepmind/formal-conjectures/blob/2411d22e1bd550d050d0eac6c1fb379a76a3e7c5/FormalConjectures/ErdosProblems/357.lean) was fetched in full and compared byte-for-byte with the PR4918 pinned problem source: **they are identical**. In particular its lower-density proof remains `sorry`.

## Repository and dependency boundaries

The complete recursive Git trees at both pinned KitaKen1 commits contain exactly two Lean files each: the FC-linked source audited above and a `lean4web` standalone rendition. Both standalone files were fetched in full and compared against the corresponding fully read FC source. Their additional lines reproduce the problem definitions, the identity `answer` macro, adjusted namespaces, and the same finite-growth endpoints. They introduce no additional infinite-sequence argument or density theorem. These standalone files are not imports of the FC-linked proofs.

This review covers the **complete problem-specific custom proof sources**, their manifests, and both exact pinned imported problem statements. It does **not** reread every transitive Mathlib/Batteries/tactic/`FormalConjecturesUtil` library file, regenerate their compiled declaration closure, recompile the earlier Lean versions, or independently certify their published axiom reports. No such exhaustive library audit is needed to distinguish the explicitly read finite-construction arguments from the current infinite-sequence counting proof, but that limitation must remain clear.

The appropriate scoped statement is: **no complete proof of the new infinite lower-density endpoint, or its general linear-growth obstruction, occurs in the reviewed prior problem-specific sources.** This does not establish absence from all other repositories or a globally first formalization. The existing submissions remain credited prior finite-growth formalizations.
