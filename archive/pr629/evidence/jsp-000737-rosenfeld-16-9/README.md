# JSP-000737 / Erdős 886: an infinite four-divisor family

This packet proves the complete known `rosenfeld_infinite` variant: infinitely many natural numbers `n` have at least four distinct divisors in the **open** interval

$$\bigl(\sqrt n,\;\sqrt n+16n^{1/4}\bigr).$$

It also proves the stronger constant `9` for infinitely many `n`. The formal definition and the constant-16 endpoint exactly match the [pinned Formal Conjectures source](https://github.com/google-deepmind/formal-conjectures/blob/40e7c98697de6f66b8cbdbf641749ab39ed9c152/FormalConjectures/ErdosProblems/886.lean).

**This is a known lower construction and an attributed formalization refinement. It does not solve the main open all-epsilon upper-bound problem, prove that there are exactly four divisors, or establish a globally optimal constant.**

## Construction and proof

For a natural parameter `a`, let `N(a) = a(a+1)...(a+7)`. Use the following four divisors and their complementary factors:

| Selected divisor | Complementary factor |
| --- | --- |
| `A0=(a+1)(a+2)(a+4)(a+7)` | `B0=a(a+3)(a+5)(a+6)` |
| `A1=(a+1)(a+2)(a+5)(a+6)` | `B1=a(a+3)(a+4)(a+7)` |
| `A2=(a+1)(a+3)(a+4)(a+6)` | `B2=a(a+2)(a+5)(a+7)` |
| `A3=(a+2)(a+3)(a+4)(a+5)` | `B3=a(a+1)(a+6)(a+7)` |

Each `Ai*Bi=N`, and `B0<A0<A1<A2<A3`. For `a≥1`, positivity and `A0*B0=N` therefore give `B0<sqrt(N)<A0`. The cross-pair gap has the particularly useful identity

$$A_3-B_0=8(a+3)(a+5).$$

Since `N≥a^8`, its fourth root is at least `a^2`. For `a≥10`, the displayed gap is at most `16a^2`; for `a≥66`, it is at most `9a^2`. Combining these bounds with the **strict** inequality `B0<sqrt(N)` places every selected divisor strictly below the required upper endpoint. The lower endpoint is strict because `sqrt(N)<A0`.

The four divisors are distinct, so they form a four-element subset of the exact `Nat.divisors` filter. Finally, `N(a)≥a` and the choice `a=max(cutoff,M+1)` produce a qualifying `N>M` for every bound `M`. Infinitude is thus proved for the integers `N`, not merely for parameter values or a finite list of samples.

## Exact endpoints

```lean
theorem Erdos886.erdos_886.variants.rosenfeld_infinite :
    Set.Infinite {n | 4 ≤ (Erdos886.Erdos886Divisors n (1/4) 16).card}

theorem Erdos886.rosenfeld_infinite9 :
    Set.Infinite {n | 4 ≤ (Erdos886.Erdos886Divisors n (1/4) 9).card}
```

The definition uses `(Nat.divisors n).filter` with both comparisons strict and with exponent `1/2-ε`, exactly as upstream. There is no floor/ceiling replacement, reconstruction hypothesis, finite cutoff on the quantified conclusion, or imported unfinished theorem.

## Prior work and actual contribution

The mathematical construction belongs to P. Erdős and M. Rosenfeld, *The factor-difference set of integers*, Acta Arithmetica 79 (1997), 353–359, Proposition 4.2 ([DOI](https://doi.org/10.4064/aa-79-4-353-359), [publisher PDF](https://matwbn.icm.edu.pl/ksiazki/aa/aa79/aa7944.pdf)). The construction and proposition were checked through the indexed publication text and linked formal sources; no successful direct PDF visual inspection is claimed.

Jarek Koch's [prior public formalization](https://github.com/jarekkoch-hub/erdos887-lean/blob/230bf2cd0bc15f971ad9d0e36f36f2056dd9d8b7/Erdos887/Formalization.lean) already constructs this infinite four-divisor family with constant **64**. Its elementary definitions and arithmetic identities are adapted here with the original MIT notice. The prior source was inspected; this project did not replay that entire source or its conditional upper-bound development. The present packet freshly checks its own adapted arithmetic module and proves the tighter **16 and 9** bounds plus the exact open-filter bridge. It does not present the underlying family as new.

Related prize [PR #450](https://github.com/TheJustinSunPrize/awards/pull/450) concerns a different upper-bound result; [PR #489](https://github.com/TheJustinSunPrize/awards/pull/489) concerns a five-divisor family with constant 31. A bounded search did not locate a complete existing formalization of this exact constant-16 variant or this constant-9 endpoint. This does not establish first priority or mathematical novelty, and no unqualified first-formalization claim is made.

**Gott-L** proposed and initiated the project, set its overall objectives and research direction, and owns and authorizes this submission. **OpenAI Codex** performed the research, proof adaptation, sharper estimates, Lean implementation, documentation and internal checks. Erdős–Rosenfeld and Koch retain their preceding mathematical and formalization credit. Internal agent review is not independent human peer review or official prize verification.

## Reproduction and evidence

Lean `4.19.0` and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b` are pinned. Transitive package revisions appear in `lake-manifest.json`. After fetching the pinned dependencies, the selected cache roots are:

```text
lake exe cache get Mathlib.Analysis.SpecialFunctions.Pow.Real Mathlib.NumberTheory.Divisors Mathlib.Tactic.Linarith
python verify.py
```

`verify.py` recompiles `E886Construction.lean`, `E886Window.lean`, and `E886.lean` in a new temporary directory, excludes old project build files, audits all 28 named proof declarations, and checks the exact filter definition and both infinite-set endpoint types. It permits only `propext`, `Classical.choice`, and `Quot.sound`; `sorryAx` is rejected. The standard pinned Mathlib cache is trusted as the dependency environment. This is not a from-source rebuild of Mathlib or a second kernel implementation.

All three proof modules passed final fresh compilation with warnings treated as errors. All 28 named axiom audits and the three definition/endpoint type checks passed; the two endpoints depend only on the three allowed standard axioms. Exact source hashes and results are recorded in [verification.json](verification.json). A different Codex agent independently repeated fresh compilation, all 28 audits, and three additional checks including fully expanded interval predicates; see [internal-review.md](internal-review.md). Both runs use the same Lean kernel implementation and the pinned dependency cache.

## Licenses

`E886Construction.lean` and `E886Window.lean` use MIT; the adapted construction retains Jarek Koch's original notice. `E886.lean` and `verify.py` use Apache-2.0, including the upstream definition/statement attribution. See `LICENSE`, `LICENSE-MIT`, and `NOTICE`. Documentation uses CC BY 4.0. Dependencies retain their own licenses and are not included in the public packet. No private contact or payment information is published.
