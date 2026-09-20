# JSP-000746 / Erdős 895: internal source and semantic review

2026-09-20. **PASS for the exact sources below; no blocking defect found.** I read TrianglePatterns, FiniteBridge and the final Main in full and reconstructed their arguments. I also read Audit and its actual output. I authored PositiveIdempotent in this same session and participated in the common implementation discussion. This is a same-team review, not an external independent verification or a clean-room claim. No proof source was edited during this review, and I did not repeat the other authors' compilations.

## Fixed sources reviewed

| File | Bytes | SHA256 |
| --- | ---: | --- |
| TrianglePatterns.lean | 4,250 | `8e2cf6f394ca8312b96b82b00970f73e555ee16d2e51f7095fc6771599bdeba7` |
| FiniteBridge.lean | 5,759 | `e375533ae4d20a936ab454d0b939ebb16d3e03ae95f38f95345e26fec71189c8` |
| Main.lean | 3,049 | `9cb9ec2d74ed017ac2a247c23c8141f97fb6186e284de8641aca787119102e19` |
| PositiveIdempotent.lean | 2,073 | `50ba0677486033726c85197720a11bf02b1878a7487ee191e2fbff304e7b1d64` |
| Audit.lean | 915 | `5be4cfbf3f54a1e4dc0cfc5fba2d80c31e2e4c5f744d77c6dd8d7955377af80f` |

I initially read Main before its finite endpoint was added, then read the complete final file above. This PASS applies to the final hash, which imports FiniteBridge and contains the unconditional `erdos_895` theorem, not only the preliminary infinite statement.

## Mathematical and statement checks

TrianglePatterns preserves the order of every nested ultrafilter quantifier. `eventually_add_first` expands `(a+b,c)` and `eventually_add_second` expands `(a,b+c)` using idempotence; neither exchanges variables. In the right-summand contradiction the actual edges are `R(c,b+c)`, `R(b+c,a+(b+c))` and `R(c,(a+b)+c)`. Associativity supplies the shared endpoint. The direct and left-summand arguments likewise intersect finitely many eventual conditions before choosing witnesses. There is no Fubini assumption, commutativity assumption on this generic semigroup, or presumption that the ultrafilter product is commutative. The generic triangle prohibition is exactly the displayed hypothesis and is later obtained from an actual simple graph.

Main chooses distinct summands using singleton avoidance, then orders them. Only this ordering step uses symmetry and commutativity of positive-integer addition. Since `0 < a < b`, the sum is also distinct from both summands. The graph conversion uses actual adjacency and `CliqueFree 3`; looplessness ensures a triangle's three vertices are distinct. `integer_schur` restricts an arbitrary graph on all integers to positive integers and returns positive, ordered witnesses, without restricting the original graph's domain or its other edges.

FiniteBridge proves uniformity in the correct order: `exists N, forall n >= N, forall G`. Negating this produces finite counterexamples of sizes `size k >= k`. `boundedPullback` keeps exactly the in-range original edges and isolates out-of-range points; triangle-freeness is preserved. The ultrafilter limit is an actual symmetric, loopless graph. Any triangle in the limit would give all three original edges at the same index by a finite intersection. Conversely, the limit's three nonedges become three eventual nonedges using the ultrafilter dichotomy, not an invalid complement rule for general filters. The size bound is intersected with those same three conditions before selecting one index. Thus the witnesses really lie in that finite graph and contradict its asserted failure.

The finite labels are correct: label `i : Fin n` denotes the positive integer `i.val+1`. Hence the sum label is `a.val+b.val+1`, with the separate strict bound `< n`. The proof establishes `(a+b).natPred = a.natPred+b.natPred+1` and uses it consistently. The summands satisfy `a.val < b.val`, so neither equality of summands nor a zero label interpreted as the integer zero is a loophole.

Finally, `erdos_895` applies `eventual_finite_schur_explicit_of_infinite positive_schur`; its intermediate `hInfinite` premise is fully discharged. The endpoint has no idempotent, compactness, finite-colouring, decidability, or infinite-graph hypothesis left for a caller to supply. It proves the qualitative eventual finite statement; it does **not** assert a numeric threshold such as 18, optimality, a new mathematical result, or priority over earlier complete implementations.

## Imports, axioms and actual checks

I recursively read import headers from the actual local source roots, removing nested comments and including implicit Init imports. The four mathematical root modules resolve to **2,250 modules**, with zero unresolved imports: 4 project, 743 Mathlib, 1,272 Lean/toolchain, and 231 modules from the standard pinned support packages. Audit imports only Main, so including Audit gives 2,251. No old Erdős/JSP/plby problem-specific source occurs in the resolved import closure. There is no blanket `import Mathlib`.

The four project mathematical files contain no `axiom`, `sorry`, `admit`, `native_decide` or `bv_decide` command after comments are removed. Their full proofs do not invoke a SAT/LRAT certificate or load the earlier finite-certificate proof. This must not be misstated as absence of SAT/LRAT modules from the entire import closure: ordinary Lean/Std tactic imports do include BVDecide/LRAT checker and SAT utility modules. Presence of those general tools is distinct from their use to prove this theorem.

I read [Main's actual compile record](logs/main-root-01/result.json): exit 0, source unchanged, the final Main hash above, 8.5 seconds, and warnings treated as errors. I read [Audit's actual compile record](logs/audit-root-01/result.json) and [all 19 axiom results](logs/audit-root-01/stdout.txt): exit 0, final Audit hash above, 8.828 seconds. Every result lists only `propext`, `Classical.choice`, `Quot.sound`, or a subset. In particular, the final finite endpoint lists no `sorryAx` or custom assumption. Audit stdout SHA256 is `05806f28e7db075a346e3106f193be78dd532270964bcf987cae117322a37e68`.

My own PositiveIdempotent compilation also passed in [positive-c-03](logs/positive-c-03/result.json). Its proof obtains an Ellis idempotent and excludes a principal one by the impossibility of `a+a=a` for a positive integer; the cofinite and unboundedness helpers do not assume freeness as an axiom.

These are local Lean checks using the shared pinned dependency caches and newly built missing modules. I did not rebuild every transitive dependency, independently replay the Lean kernel in another checker, compare every cached object to its source, or verify a fresh standard Lake build in this review. The source-level closure check and the read-back axiom logs do not imply those stronger claims. Known prior mathematics and complete formalizations remain prior work; this review establishes the displayed implementation's scope and found no hidden problem-specific premise.
