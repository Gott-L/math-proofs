# Complete lacunary-difference coloring theorem in Lean

This package gives a newly written Lean implementation of the complete finite
coloring question [JSP-000745](https://github.com/TheJustinSunPrize/awards/blob/cdec393dd0447e8be11f5d2117e165f79e4154bb/problems/catalog-0701-0800.md#JSP-000745),
also known as [Erdős 894](https://www.erdosproblems.com/894).
It is not a new mathematical discovery or a first-formalization claim.

## Full theorem

For every positive integer sequence `a` with a uniform growth ratio greater
than one, there are a positive number `N` and a coloring of **all integers**
by `Fin N` such that no difference `a k` occurs between two points of the same
color. The result simultaneously covers every index and every pair of integers.

The root is `GottL894.lacunary_difference_coloring` in [Main.lean](Main.lean).
[Audit.lean](Audit.lean) repeats the full statement and prints its transitive
axiom dependencies. Exchanging the two integer variables handles both signs,
so the positive-difference formulation is equivalent to avoiding absolute
differences in the sequence. No fixed ratio, finite prefix, or assumed rotation
is substituted for the original problem.

## Mathematical proof

Choose a positive stride `r` so that `(1 + ε)^r ≥ 4`, and split the sequence
according to its index modulo `r`. Each resulting subsequence `m` grows by a
factor of at least four. Construct nested nonempty closed intervals
`[(z_j+1/4)/m_j, (z_j+3/4)/m_j]`: given the current left endpoint `l`, choose
`z_(j+1) = ceil(m_(j+1) l - 1/4)`. The ceiling inequalities and factor-four
growth put the new interval inside the old one. The supremum of the left
endpoints belongs to every interval, supplying a real rotation `θ` whose
sampled values stay in integer translates of `[1/4,3/4]`.

For this rotation, color an integer `x` by `floor(4 θ x) mod 4`. If two colors
coincide, their floor difference is divisible by four. A difference landing
in the closed middle half instead forces that floor difference strictly
between `4z` and `4z+4`, a contradiction. Take the product of the `r`
four-colorings and identify its finite color type with `Fin N`.

This is the classical elementary argument described in the introduction,
pages 1–3, of Yuval Peres and Wilhelm Schlag,
[*Two Erdős problems on lacunary sequences: chromatic number and Diophantine approximation*](https://arxiv.org/abs/0706.0223),
Bull. London Math. Soc. 42 (2010), 295–300. Their sharper quantitative estimate
is a different, stronger result and is not claimed here. Historical mathematical
credit, including the earlier works discussed in that paper, remains with
those authors. [scope.md](scope.md) records the original-statement comparison.

## Attribution and known prior formalizations

Gott-L initiated the project, proposed its objectives, and planned its research
direction. Codex performed mathematical reconstruction, wrote these Lean files,
and conducted internal checks. Internal reviewers are members of the same
Codex team; they are not official or independent human verifiers.

Known complete prior work includes
[plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos894.lean)
and [official PR344](https://github.com/TheJustinSunPrize/awards/pull/344), whose
selected proof is at `87ea0ab4ebf1d04d9a62341f8a9025e3a713bfd6` in
`CollinYuanjieRen/awards`. Prior source audits informed topic selection, so
this is not a clean-room claim. No problem-specific Lean source from those
implementations is copied or imported by this package. Its only external
proof dependency is Mathlib and its pinned dependencies.

PR1186 and PR1271 also record upstream work. This later implementation does
not assert priority over any earlier complete proof or request displacement
of an accepted earlier source. Submission, local checking and correctness do
not establish award entitlement. Maintainers must determine acceptance,
authorship, priority and any applicable recognition under the current rules.

## Reproduction

The toolchain is Lean 4.19.0; Mathlib is pinned to
`c44e0c8ee63ca166450922a373c7409c5d26b00b`, with transitive pins in
`lake-manifest.json`. From this package directory in a normal Lean installation:

```sh
lake exe cache get
lake build
lake env lean -t 0 -DwarningAsError=true Audit.lean
```

The recorded local check directly compiles all five modules into an initially
empty output directory using that Lean version, warning errors enabled and
trust level zero, then performs the typed statement and named axiom audit.
See `verification/report.md` for the actual execution and trust boundaries.
The local check reuses existing pinned dependency objects; it is not a fresh
source build of all Mathlib, an independent-kernel replay, or official review.

Public correspondence: **649148013@qq.com**.
