# Finite-prefix extension for separated multiplicative systems

This package formalizes a known extension theorem associated with Erdős problem 951 / JSP-000791. Every finite increasing list of real generators greater than one, whose distinct natural exponent vectors give products at distance at least one, extends to an infinite sequence with the same property.

The extension argument is credited to Barreto–Price and to Patrick White with Claude, as discussed in the [working report, §4](https://www.erdosproblemaday.com/report/951). The implementation below uses inverse-square-root weights and a countable union estimate. This choice of proof organization is not a claim of mathematical discovery or global formalization priority. Source pins, attribution boundaries, and licenses are recorded in [SOURCES.md](SOURCES.md).

## Exact statement

For `a : Fin n → ℝ`, set

\[
m_a(u)=\prod_{i<n}a_i^{u_i},\qquad u\in\mathbb N^n.
\]

`Separated a` means

\[
u\ne v\quad\Longrightarrow\quad |m_a(u)-m_a(v)|\ge1
\]

for **all distinct exponent vectors**, including the zero vector. This condition also rules out equal products with different exponent representations. It is stronger than separation restricted to unequal numerical products.

The public endpoint `E951.finite_prefix_extension` assumes `∀ i, 1 < a i`, `StrictMono a`, and `Separated a`. It concludes that there exists `b : ℕ → ℝ` such that:

- `b` is strictly increasing and every `b i` is greater than one;
- `b i = a i` at every original index;
- every two distinct finitely supported natural exponent vectors on `ℕ` give products at distance at least one.

There is no exponent cutoff, no bound on the length of the initial prefix, and no extra extension or summability hypothesis in this endpoint. The statement includes `n = 0`.

## Summable weights

Assume every `a i > 1`, without yet requiring separation. Define

\[
w(u)=m_a(u)^{-1/2},\qquad
Z=\sum_{u\in\mathbb N^n}w(u)
 =\prod_{i<n}\frac1{1-a_i^{-1/2}}.
\]

Each coordinate gives a convergent geometric series. `E951Weights.lean` proves the finite product identity by induction on the number of coordinates, splitting an exponent vector into its first coordinate and its remaining coordinates. It supplies `HasSum (weight a) Z`, positivity, and the corresponding nonnegative extended-real sum. For the empty prefix, the exponent-vector space has one element and `Z = 1`.

All later sums run over exponent vectors directly. Neither injectivity of the monomial map nor a finite counting estimate for bounded monomials is needed for these analytic bounds.

## A bound for one forbidden set

Choose `S ≥ 4` and use the window

\[
I=[S^2,2S^2],\qquad \operatorname{vol}(I)=S^2.
\]

For `s,t ≥ 1` and `d = k+1 ≥ 1`, define

\[
F(s,t,k)=\{x\in I:|s x^{k+1}-t|<1\}.
\]

`E951Intervals.lean` first proves a diameter estimate. If `x ≤ y` lie in this set, then

\[
s(S^2)^k(y-x)\le s(y^{k+1}-x^{k+1})<2.
\]

The first inequality follows from an elementary power-difference bound. A derivative is unnecessary. Any nonempty forbidden set therefore lies in an interval centered at one of its members, with radius `2 / (s (S²)^k)`. Its outer measure is at most

\[
\frac4{s(S^2)^k}.
\]

The empty case is handled separately. Nonemptiness also gives the deliberately loose estimate

\[
\sqrt t\le 2\sqrt s\,(2S)^{k+1}.
\]

Indeed, a forbidden point satisfies `t < s x^(k+1) + 1`, while `x ≤ 2S² ≤ (2S)²`; squaring the proposed right-hand side gives a sufficient upper bound. Combining this with the interval estimate yields the universal bound

\[
\operatorname{vol}(F(s,t,k))
\le
\frac{8S^2(2/S)^{k+1}}{\sqrt s\sqrt t}. \tag{1}
\]

The formal theorem `badSet_volume_le` has no nonemptiness or measurability premise. Volume is used through its outer-measure inequalities on arbitrary sets.

## Avoiding every forbidden set at once

Take `s = m_a(u)` and `t = m_a(v)`. The union ranges over **all** `u,v : Fin n → ℕ` and `k : ℕ`, a countable family. Countable subadditivity and (1) give

\[
\begin{aligned}
\operatorname{vol}\!\left(\bigcup_{u,v,k}F(m_a(u),m_a(v),k)\right)
&\le 8S^2\sum_{u,v,k}(2/S)^{k+1}w(u)w(v)\\
&\le 32S Z^2. \tag{2}
\end{aligned}
\]

For the final inequality, put `q = 2/S ≤ 1/2`. Then

\[
\sum_{k\ge0}q^{k+1}=\frac q{1-q}\le2q=\frac4S.
\]

`E951Series.lean` proves the triple-sum bound with nonnegative extended-real sums, so no unjustified rearrangement of conditionally convergent series is involved. The argument does not count possible values of `v` for each `u,k`; it sums their weights directly.

Given any real cutoff `B`, choose

\[
S>\max\{4,B,32Z^2\}.
\]

Then the bound in (2) is strictly less than `S²`, the measure of the window. Some `x ∈ I` lies outside the entire forbidden union. Because `S ≥ 4`, we have `x ≥ S² ≥ S > B` and `x > 1`. This proves `exists_avoiding_above`: for every `u,v,k`,

\[
|m_a(u)x^{k+1}-m_a(v)|\ge1.
\]

This statement includes `u = v`; omitting those pairs would leave a gap when comparing new exponent vectors.

## Appending a generator and passing to a sequence

Assume the old prefix is separated. Write two products after appending `x` as `m_a(u)x^r` and `m_a(v)x^s`.

- If `r = s`, distinctness of the full exponent vectors forces `u ≠ v`. Old separation multiplied by `x^r ≥ 1` supplies the required gap.
- If `r > s`, factor out `x^s`. The remaining difference is covered by the avoidance theorem with positive exponent `r-s`. The case `s > r` follows by swapping the products.

`E951Append.lean` proves this split, and `extension_step` supplies a new separated prefix above any prescribed cutoff.

`E951Sequence.lean` iterates the step. At each stage it chooses the next generator above the sum of the old positive generators, hence above every old entry. For an empty prefix the sum is zero, and the separately established bound `x > 1` still applies. The resulting sequence is defined by stable prefix entries; no analytic limit is used.

Two finitely supported exponent vectors fit into one common finite stage. The proof establishes both product preservation and preservation of distinctness when restricting them to that stage. Finite-stage separation therefore proves `SequenceSeparated` for the infinite sequence.

## Scope and review boundary

This is an extension theorem, not a proof or disproof of the eventual prime-counting assertion in the pinned Erdős 951 statement. Arbitrarily large choices of new generators do not establish repeated counting violations at arbitrarily large cutoffs. The package also does not certify a numerical near-optimal three-generator example.

The pinned prize catalogue records JSP-000791 as **Eligible to claim: No**. This package makes no award entitlement or payment claim.

The outline describes the implemented mathematical argument. Build, axiom, and replay results belong to the package's separate verification records. The internal mathematical review included the authoring agent for `E951Intervals.lean`; it is not presented as an independent external review.

Original documentation in this package is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The new Lean implementation uses Apache-2.0. These licenses do not relicense cited third-party material.
