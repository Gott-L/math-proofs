# JSP-000746 / Erdős 895: independent Schur triples

This project gives a complete Lean 4.19.0 formalization of the qualitative independent-Schur-triple problem, using additive idempotent ultrafilters and compactness. The mathematics and the use of ultrafilters in this subject predate this project. This is a later implementation, not a new resolution or a first-formalization claim.

## Complete statements

For every triangle-free simple graph on the positive integers, there exist positive integers `a < b` such that the three distinct vertices `a`, `b`, `a+b` are pairwise nonadjacent. The same conclusion holds in a triangle-free graph on all integers, with positive witnesses.

The original eventual finite version is also proved:

> There is a natural number N such that for every n ≥ N and every triangle-free graph on {1,...,n}, there are a < b with a+b ≤ n for which a, b, a+b are pairwise nonadjacent.

The unconditional endpoint is `GottL746.erdos_895` in [Main.lean](Main.lean). In its `Fin n` encoding, label `i` denotes positive integer `i.val+1`, so the sum's label is `a.val+b.val+1`. The endpoint quantifies over every sufficiently large size and every graph at that size. The infinite theorem used in the compactness bridge is fully proved and instantiated, not an additional assumption.

The additional endpoints `positive_schur` and `integer_schur` give the two infinite graph formulations. This implementation does not give the explicit sharp threshold 18, a sharp edge bound, or any infinite independent finite-sums-set strengthening.

## Argument

Take an additive idempotent ultrafilter U on the positive integers, using Mathlib's compact-semigroup idempotent theorem. It is nonprincipal: a principal idempotent at a positive integer t would imply t+t=t. It therefore contains every cofinite set.

Write L(P) for “for U-many a, for U-many b, P(a,b),” keeping this quantifier order. Idempotence lets us replace the first variable by a+b, or, at fixed first variable, the second by b+c. No exchange of ultrafilter quantifiers is used.

For a triangle-free adjacency relation R, none of these three patterns can be L-large:

1. R(a,b): this would give a triangle on a,b,c.
2. R(a,a+b): the three instances give a triangle on a,a+b,(a+b)+c.
3. R(b,a+b): the three instances give a triangle on c,b+c,(a+b)+c.

The ultrafilter dichotomy makes the complements of all three patterns simultaneously large. Intersecting with a≠b gives the required independent triple, which can be ordered using symmetry and commutativity of ordinary addition.

For the finite statement, arbitrarily large counterexamples would produce a sequence of triangle-free finite graphs of sizes at least k. Extend each to the positive integers, isolating out-of-range vertices, and take an ultrafilter limit of each adjacency decision. The resulting infinite graph is triangle-free. Its independent Schur triple transfers to one sufficiently large finite member, contradicting the counterexample property. [FiniteBridge.lean](FiniteBridge.lean) supplies this uniform-threshold argument.

## Reproduction

Use the compiler pin in [lean-toolchain](lean-toolchain) and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` in [lake-manifest.json](lake-manifest.json). From this directory:

```sh
lake exe cache get
python verify.py --label my-check
```

See [VERIFICATION.md](VERIFICATION.md) for the executed commands, source hashes, outputs and dependency-cache limitations. [Audit.lean](Audit.lean) prints the named axiom dependencies of all 19 project theorems. Internal semantic and source-import review is recorded in [REVIEW-C.md](REVIEW-C.md).

## Prior work and contribution

[HISTORY.md](HISTORY.md) documents primary historical sources, including Deuber, Gunderson, Hindman and Strauss (1997), and Łuczak, Rödl and Schoen (1998), and separates qualitative existence from Barber's explicit finite bound. Prior complete Lean implementations include [plby's pinned E895 source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos895.lean), [official PR165](https://github.com/TheJustinSunPrize/awards/pull/165), and [PR402](https://github.com/TheJustinSunPrize/awards/pull/402). Related earlier records, including [issue18](https://github.com/TheJustinSunPrize/awards/issues/18), [issue19](https://github.com/TheJustinSunPrize/awards/issues/19), [PR738](https://github.com/TheJustinSunPrize/awards/pull/738) and [PR1386](https://github.com/TheJustinSunPrize/awards/pull/1386), must be considered in any priority review. This list is not a worldwide priority search.

Earlier problem-specific source was read during selection and comparison; this is not a clean-room claim. No such source or certificate was copied or imported into the new four mathematical modules. Their implementation uses idempotent ultrafilters and an explicit finite-graph compactness bridge instead of a finite SAT certificate. Standard tactic dependencies can contain general SAT/LRAT infrastructure; this project does not invoke those proof procedures. Earlier certificate proofs also check their proofs in Lean; no first kernel-checking, smaller trusted base, performance improvement or new mathematical-method claim is made here.

Gott-L initiated the project, proposed its objectives, planned the work and directed the research. Codex reconstructed the mathematics, researched sources, implemented the Lean proof and performed internal checks, including parallel component development and cross-review. This review is same-team checking, not independent human verification. Historical mathematical authors and earlier formalizers retain their attribution and rights. The new implementation is released under [MIT](LICENSE).

Contact: `649148013@qq.com`. Acceptance, source registration, priority and any award remain decisions for the organizers; none is asserted by this repository.
