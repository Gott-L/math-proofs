# JSP-000897: dependency review

**PASS for the source-level dependency claim.** The new implementation does not import the Turán module or use a Turán graph or the exact clique-extremal formula. This review makes no comparative speed, novelty, or prize claim.

## Actual scope and method

On 2026-09-20, reviewer C recursively read the actual Lean import headers of Main, JoinBound, NeighborhoodBound, DegreeBound, and Audit. Headers were parsed after skipping nested comments and whitespace; traversal stops at the first non-header command, so quoted examples later in compiler sources are not mistaken for imports. Implicit `Init` imports were included for non-prelude files. Every reached module resolved to source under the project, the pinned local package sources, or the Lean 4.19.0 source distribution. The machine-readable [record and complete module list](dependency-review-c.json) gives the source roots and exact root identities.

The closure contains **2381 modules**, including the five project roots: 870 Mathlib modules, 1272 Lean/Std/toolchain modules, and 234 modules from the other standard packages. No module name contains `Turan`. A complete raw-text search of the resolved source files found no `turanGraph`, Turán graph edge-count formula identifier, or `extremalNumber_top`. Its only two ASCII `Turan` matches are in the opening documentation comment of DegreeBound, line 8; both state that this dependency is absent. No unresolved import was silently skipped.

| Root source | Bytes | SHA-256 |
| --- | ---: | --- |
| Main.lean | 3314 | `10c81035619eab00f86a4a1381e945cc6b024862c8fe882ea406b759a71f8260` |
| JoinBound.lean | 5501 | `6eddc1bdf38a9237df5880ab0d7d88e95e898039bf352d3cbf034c80e4773075` |
| NeighborhoodBound.lean | 3375 | `061450968678033f52dd8d8b33da967a7e646e5d8fcbaf4a6a66eb0148b897ad` |
| DegreeBound.lean | 2753 | `b23910886ae63b60a2e7c8ee979bec7ac7ef80ce5754a1100859d841be6f6de6` |
| Audit.lean | 959 | `a7ececeaac3d24edb55d2cbbe7e746de8dee072aa58259ff8db9945af1a2e953` |

## What replaced the dependency

JoinBound obtains a genuine finite maximizing clique-free graph from the definition of `SimpleGraph.extremalNumber`. Joining it to an independent set proves

`ex(d, K_(r-1)) + d*(n-d) <= ex(n, K_r)`

without evaluating either extremal number. NeighborhoodBound counts edges using the actual induced open neighborhood and degrees outside it. Main combines those two inequalities; it introduces no Turán formula as a hypothesis. DegreeBound uses the join inequality at `d = n/2`, discards a nonnegative term, and combines the resulting balanced-product lower bound with the degree sum and exact odd/even arithmetic. Thus the uniform `n <= 2*maxDegree` conclusion likewise needs no Turán evaluation.

## Comparison limited to the inspected earlier source

The previously read source is `../screen-full-c/plby-1079.lean`, 18306 bytes, SHA-256 `09efec8509c86a61575eed184fd68d76d09a4f74ca94b7338478cb5657f9cae3`. It already contains complete non-strict and strict endpoints; this audit does not identify a missing theorem in that implementation.

Its relevant actual source locations are:

- Line 23 imports `Mathlib.Combinatorics.SimpleGraph.Extremal.Turan`.
- Lines 201–218 use a Turán graph join, with `extremalNumber_top` at line 212.
- Lines 294–309 convert both extremal numbers to Turán edge counts; the formula rewrites are at lines 300–301.
- Lines 357–364 prove the balanced-square estimate using `card_edgeFinset_turanGraph` and `card_edgeFinset_turanGraph_add` at lines 360–363.
- Lines 368–378 use the bipartite Turán graph and its clique-freeness; lines 387–397 feed those results into the degree bound.

These are verifiable differences in mathematical dependencies. The old source uses Lean 4.33, whereas this package uses Lean 4.19. The earlier package was not rebuilt or benchmarked here, so no runtime, proof-size, or transitive-module-count comparison is asserted.

## Limits and provenance

This is an import/source review, not an export of the exact constants used by each proof term: the full import closure can be much larger than that proof-term dependency set. Existing standard dependency objects were not rebuilt or independently matched to every source by this review, and no additional compilation or independent kernel replay was run. The machine record preserves all module names and the five root hashes; it does not pretend to certify the full compiler or cached dependency binaries.

Reviewer C authored DegreeBound and participated in the same project team. Consequently this dependency audit is not an external independent review of the entire proof. Earlier complete formalizations were read before implementation and are disclosed; removal of a particular theorem dependency does not establish historical priority or official eligibility.
