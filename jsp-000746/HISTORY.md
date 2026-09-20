# Historical and mathematical provenance

2026-09-20. This repository formalizes a known qualitative theorem. It does
not claim a new mathematical solution, the first use of ultrafilters for
this subject, or the first complete Lean implementation.

## The older independent-Schur result

Tomasz Łuczak, Vojtěch Rödl and Tomasz Schoen proved substantially more
than the existence of an independent triple `a,b,a+b` in a triangle-free
graph. Their paper, *Independent finite sums in graphs defined on the
natural numbers*, Discrete Mathematics **181** (1998), 289–294,
[DOI 10.1016/S0012-365X(97)00064-2](https://doi.org/10.1016/S0012-365X(97)00064-2),
contains its main result as **Theorem 5 and Corollary 6, p. 293**.
In particular, for any fixed finite sum length and any fixed forbidden
clique, an infinite set can be chosen whose sums of up to that length are
independent. The independent Schur triple is a special case.
The paper's **p. 291, Theorem 1 and the discussion preceding Theorem 3**,
uses Milliken–Taylor and explicitly distinguishes its argument from
ultrafilter or dynamical methods. The six-page primary text is readable
in this [public full-text copy](https://www.academia.edu/77319140/Independent_finite_sums_in_graphs_defined_on_the_natural_numbers).

The attribution is independently explicit in David S. Gunderson, Imre
Leader, Hans Jürgen Prömel and Vojtěch Rödl, *Independent arithmetic
progressions in clique-free graphs on the natural numbers*, JCTA **93**
(2001), 1–17. In the linked [author preprint, p. 2, Question 1.2 and
Theorem 1.3](https://www.cs.umd.edu/~gasarch/TOPICS/vdw/ArithSeqInGraphs.pdf#page=2),
they credit the independent-Schur answer and the more general finite-sums
result to Łuczak–Rödl–Schoen, using Milliken–Taylor. Page numbers here refer
to the 14-page preprint, not the journal pagination.

## Finite sums and the infinite question are different

Walter Deuber, David Gunderson, Neil Hindman and Dona Strauss,
*Independent Finite Sums for K_m-Free Graphs*, JCTA **78** (1997),
171–198, [DOI 10.1006/jcta.1996.2760](https://doi.org/10.1006/jcta.1996.2760),
already records the Łuczak–Rödl–Schoen finite result as **Theorem 1.5**,
citing their then-unpublished manuscript.

Its **Theorem 2.2** constructs a triangle-free graph with no independent
set consisting of all nonempty finite sums from an infinite sequence.
Thus this unrestricted infinite strengthening is false, not an open
extension of the theorem proved here. **Theorem 3.19 / Corollary 3.20**
give a weaker infinite conclusion for sums with disjoint index supports;
that does not directly supply the overlapping-support pairs in
`{a,b,a+b}`. **Theorem 4.14 / Corollary 4.15** give the full infinite
finite-sums conclusion under the stronger exclusion of a complete
bipartite graph. See the [author PDF](https://nhindman.us/research/graphs.pdf),
respectively pp. 2, 6–7, 18–20 and 25–26. These are author-PDF page numbers.

That same paper explicitly develops additive idempotents in `βS` in
**§1, pp. 3–5**, and uses them in **§§3–4**. The present historical check
has not located our exact three-pattern short proof in those sources;
it establishes prior use of the method, not priority for this variant.

## What this implementation contributes

Our proof specializes standard idempotent-ultrafilter reasoning to three
adjacency patterns and keeps the nested quantifier order fixed. A separate
compactness argument gives the uniform eventual finite statement. It
does not compute the explicit threshold 18 or formalize the stronger
finite-sums theorems above. Ben Barber's explicit finite-bound work,
credited in the existing problem-specific sources, must not replace
Łuczak–Rödl–Schoen's earlier credit for qualitative existence.

Earlier complete Lean proofs were inspected, including
[plby's fixed E895 source](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos895.lean)
and [official PR165](https://github.com/TheJustinSunPrize/awards/pull/165).
Their finite certificate methods already prove the qualitative question.
This repository instead writes an abstract proof using standard Mathlib
machinery; it does not import or copy their problem-specific proofs or
certificates. Prior-source inspection means this is not a clean-room claim.
The difference is the proof organization, not a claim of fewer trusted
axioms or superior performance.

The source audit read the complete 1998 paper, the relevant introduction
and references of the 2001 paper, and the 1997 definitions, theorem
statements and relevant proof sections. It is not an exhaustive priority
search. Gott-L initiated and directed this project; Codex reconstructed
and implemented the proof and performed same-team checks. Mathematical
and formalization predecessors retain their respective attribution.
