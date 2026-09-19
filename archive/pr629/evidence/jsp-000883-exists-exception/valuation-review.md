# Valuation component and verifier review

Review date: 17 September 2026. Internal technical review by the valuation sub-agent. This is not independent human verification or an organizer attestation.

## Compiled valuation component

`e1063/MaxValuation.lean` was implemented independently from the elementary prime-power divisibility argument. No Aristotle proof code was copied. Its three theorems are:

- `Erdos1063.factorization_le_dist_of_le`.
- `Erdos1063.dist_sub_sub_of_le`.
- `Erdos1063.factorization_le_offset_dist`.

Compilation with Lean 4.19.0 and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` succeeded, exit code 0, with no diagnostic output. The generated olean is under `.lake/build/lib/lean/MaxValuation.olean`. An initial invocation failed only because that output directory was missing; after creating it, the unchanged Lean source compiled successfully.

An additional `AuditMaxValuation.lean` imports that olean, checks explicit types for the general and offset valuation statements, and prints the transitive axioms of all three theorems. It compiled with exit code 0; each theorem's reported dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`.

Source SHA-256 at this review: `66e32302bd59ee29a90dfd4c153533722d3b7fb17efb5feb15d83c3fbe4f45c0`.

The argument preserves the nonzero conditions required by natural-number factorization: a and b are nonzero; a!=b gives positive distance; the offset specialization assumes i<n, j<n, and i!=j. Reflection under subtraction is proved exactly with Nat.dist, so no sign or truncated-subtraction ambiguity remains.

## Main theorem correspondence

I read the full current `Erdos1063.lean`. The stronger helper has hypotheses `2 <= k` and `k <= n`, and conclusion `exists i<k, not (n-i) divides choose(n,k)`. Its argument chooses a prime divisor of k, a factor of maximal valuation in the positive block, bounds the remaining valuations by `(k-1)!`, and contradicts the extra positive valuation from k in k!.

The final named declaration is:

```lean
theorem erdos_1063.variants.exists_exception {n k : ℕ}
    (hk : 2 ≤ k) (h : 2 * k ≤ n) :
    ∃ i < k, ¬ (n - i) ∣ n.choose k
```

This is the exact conclusion and hypotheses of the known variant in [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/1063.lean), with only metadata omitted. The wrapper derives k<=n and calls the stronger helper. There is no added premise, finite cutoff, changed notion of divisibility, or imported conjectural theorem.

This review checks the mathematical route and statement correspondence. The parent is responsible for the complete fresh compilation of all three modules and final endpoint audits; I did not run that duplicate full verification.

## Latest verify.py source review

The reviewed version converts inherited relative LEAN_PATH entries to absolute paths with respect to the project root, excludes the old `.lake/build/lib/lean` directory, prepends a fresh temporary directory, copies the three local source files there, and compiles them in dependency order: MaxValuation, OffsetProduct, Erdos1063. All local imports in the inspected sources are among these compiled modules. Thus, for the actual reviewed sources and environment, local proof dependencies are freshly compiled rather than reused from old local artifacts.

The verifier runs Lean with warnings treated as errors and checks ten fully qualified theorem names. Its parsed transitive axiom list permits only propext, Classical.choice, and Quot.sound. `sorryAx` is outside this set and is rejected even if it arises through an imported theorem rather than a literal local `sorry`. The textual local-source rejection and warning-as-error compilation give additional checks. This is a source-code assessment of that rejection behavior; I did not run a separate injected-placeholder negative control.

The receipt records the copied-and-compiled source bytes and hashes, Lean version, Mathlib commit and named axiom lists. The verifier correctly describes its method as fresh local compilation with cached dependencies. It does not rebuild Mathlib from source, certify every transitive dependency checkout, or use a second kernel implementation. Those stronger claims should not be made.

The final reviewed verifier now includes two explicit typed `example` declarations in generated Audit.lean: one demands the complete stronger theorem under k<=n, and the other demands the exact public target under 2*k<=n. I inspected those additions at lines 100–107. Both call the intended fully qualified theorem. This mechanically checks the required conclusion and hypotheses on every run, alongside the ten named axiom audits. The parent is running the final full verification after this change; this review does not claim that final execution finished before its result is available.

No public submission, prize claim, email, or remote repository mutation was performed in this subtask.
