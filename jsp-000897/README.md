# JSP-000897 / Erdős 1079: dense neighbourhoods

This project formalizes the complete non-strict dense-neighbourhood statement, its strict-threshold version, and a quantitative edge-surplus inequality in Lean 4.19.0. It uses Mathlib's actual extremal number and induced open neighbourhood. This is a later implementation of known mathematics, not a new resolution or a first-formalization claim.

## Theorems

Write `ex(n, K_r)` for the maximum number of edges in a simple graph on `n` vertices containing no copy of the complete graph `K_r`. For every `r ≥ 4`, `n ≥ 2`, and simple graph `G` on `n` vertices:

- If `e(G) ≥ ex(n, K_r)`, there is a vertex `v` of maximum degree `d` such that `2d ≥ n` and `e(G[N(v)]) ≥ ex(d, K_(r−1))`.
- If the hypothesis on edges is strict, the neighbourhood conclusion is also strict.

The endpoints are `GottL897.dense_neighborhood` and `GottL897.dense_neighborhood_strict` in [Main.lean](Main.lean). The uniform degree bound `d ≥ n/2` supplies the linear-in-`n` bound requested by the catalogue. All parameter values in the displayed ranges are included; these are not finite computational checks.

The condition `n ≥ 2` excludes the one-vertex graph: its extremal threshold and maximum degree are both zero, so it cannot satisfy the stronger conclusion `2d ≥ n`. This small-order restriction does not weaken the original asymptotic linear-degree requirement.

More generally, for `r ≥ 3` and every maximum-degree vertex `v`, `GottL897.neighborhood_surplus` proves

```
ex(d, K_(r−1)) + e(G) ≤ e(G[N(v)]) + ex(n, K_r).
```

No extra clique-freeness condition is imposed on `G`. The Lean `DecidableRel G.Adj` instance merely supports finite edge counting and can be supplied classically. The non-strict theorem includes Turán graphs. The strict theorem requires `e(G) > ex(n, K_r)`; it does not assert strictness at the equality threshold merely because `G` is not a Turán graph. We do not formalize the additional equality-case classification suggested by the problem page's “unless ... Turán graph” annotation.

## Proof and implementation contribution

Let `v` have maximum degree `d`, and put `L = e(G[N(v)])`.

1. Every edge not internal to `N(v)` has an endpoint outside `N(v)`. The sum of the degrees of those `n−d` vertices bounds their number, giving `e(G) ≤ L + (n−d)d`. Double-counting some edges only increases this upper bound.
2. Take an actual extremal `K_(r−1)`-free graph on `d` vertices. Join it to an independent set of `n−d` vertices. A clique in this join contains at most one vertex of the independent set, so the join is `K_r`-free. Its exact number of edges is `ex(d, K_(r−1)) + d(n−d)`. Thus this quantity is at most `ex(n, K_r)`.
3. Combining the two inequalities proves the surplus inequality and both neighbourhood conclusions.
4. Apply the join construction with `d = floor(n/2)` and discard its nonnegative internal edge count. This lower bound, the handshake identity and integer parity give `n ≤ 2 maxDegree(G)` under the stated threshold and `n ≥ 2`.

The contribution of this implementation is a route through the finite extremal definition and direct edge counting, without importing Turán's theorem or using a closed formula for a clique extremal number. The earlier implementation below uses Mathlib's `Extremal.Turan` and `extremalNumber_top`. See [dependency-review-c.md](dependency-review-c.md) for the source-import audit. No claim of novelty, faster compilation, smaller trusted kernel, or automatic prize eligibility follows from this change.

## Reproduction

Use the pinned compiler in [lean-toolchain](lean-toolchain) and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` in [lake-manifest.json](lake-manifest.json). From this directory, after installing the Lean toolchain:

```sh
lake exe cache get
python verify.py --label my-check
```

The verification script runs `lake build`, then a separate named-axiom audit with warnings treated as errors. The recorded execution and its dependency-cache limitations are described in [VERIFICATION.md](VERIFICATION.md). These instructions may require network access to obtain the pinned dependencies; our recorded run uses available pinned caches.

## Prior work and roles

The mathematical result is classical. Relevant historical work includes Bollobás and Thomason, *Dense neighbourhoods and Turán's theorem*, Journal of Combinatorial Theory B 31 (1981), 111–114, [DOI](https://doi.org/10.1016/S0095-8956(81)80016-0), and Erdős and Sós, *On a generalization of Turán's graph-theorem* ([paper](https://real.mtak.hu/110556/1/1983-10.pdf)). The [Erdős 1079 discussion](https://www.erdosproblems.com/forum/thread/1079) also records the strict maximum-degree strengthening associated with Bondy.

Existing complete Lean work predates this project, including [plby/lean-proofs at pinned commit 8822f7d](https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/ErdosProblems/Erdos1079.lean) and the disclosures in official [PR155](https://github.com/TheJustinSunPrize/awards/pull/155) and [PR439](https://github.com/TheJustinSunPrize/awards/pull/439). That source was read when selecting and comparing approaches. This is not a clean-room implementation or a priority claim. No problem-specific source from those implementations is copied or imported in these modules; their authors retain their own attribution and rights.

Gott-L initiated the project, proposed its objectives, planned the work and directed the research. Codex performed source research, mathematical reconstruction, the Lean implementation and internal checks, including parallel helper development and cross-review. [internal-review-b.md](internal-review-b.md) explicitly discloses that the reviewer also authored one component; this is same-team checking, not external independent verification. Historical mathematical authors and earlier formalizers retain their credit. The new implementation is released under [MIT](LICENSE).

Contact: `649148013@qq.com`. Official acceptance, source registration, priority and any award remain decisions of the prize organizers. This repository does not assert any of them.
