# Bounded prior-art refresh for the EGP package

Checked **17 September 2026, 11:05:55–11:08:11 UTC** (19:05:55–19:08:11 Asia/Shanghai).

**Result: no newly matching complete EGP upper-bound proof was found in the inspected official submissions.** This is a bounded no-hit finding, not a global priority certificate. It does not certify award eligibility, acceptance, or first-formalizer status.

## Target compared

The endpoint being checked is the universal Erdős–Goodman–Pósa theorem: for every finite simple graph on n vertices, its edges admit an exact partition into at most floor(n²/4) cliques, each consisting of either an edge or a triangle. Coverage must be exact, with no edge repeated. The open dense-graph improvement question associated with JSP-000847 / Erdős 1017 is a separate problem.

## Fresh official collection and new submissions

A read-only request through the available authenticated GitHub connector retrieved the official [all-state PR collection, sorted newest first](https://api.github.com/repos/TheJustinSunPrize/awards/pulls?state=all&sort=created&direction=desc&per_page=40). It returned 40 PRs, ranging from #670 back to #625. The newest returned PR, #670, was created at 11:04:15 UTC.

All seven returned PRs with numbers above the earlier #662 snapshot were checked by reading their complete bodies, including their claimed endpoints and scope:

| PR | Exact title | Inspected head |
| --- | --- | --- |
| [#664](https://github.com/TheJustinSunPrize/awards/pull/664) | JSP-000603: formalize exact degree certificates for magic configurations | `8f573704625910ba98cd116f4e2cda07bd2db05b` |
| [#665](https://github.com/TheJustinSunPrize/awards/pull/665) | JSP-000108: full negative answer to the subpolynomial equidistance question | `b70edb265529cc734852e8d61e169d2147e72968` |
| [#666](https://github.com/TheJustinSunPrize/awards/pull/666) | feat(candidates): add observation candidate for JSP-000301 | `a4cc6f4bf427a8f2b6dceced7040bb277c87a57c` |
| [#667](https://github.com/TheJustinSunPrize/awards/pull/667) | JSP-000082 / Erdős #64: an infinite tree of minimum degree 3 (the infinite case is trivially false) (Lean 4 + Mathlib) | `4476e8ba9858b27ea8a1e19b41661f0b81e6521f` |
| [#668](https://github.com/TheJustinSunPrize/awards/pull/668) | JSP-000879: Lean formalization — all-composite factorial differences (witness p=101) | `a1020c6536d4531412366bb31e6e4e713de4a01b` |
| [#669](https://github.com/TheJustinSunPrize/awards/pull/669) | Add JSP-000301 Lean formalization and verification evidence | `07ba342205e2dbd39be9eedabb39e0e1873b6393` |
| [#670](https://github.com/TheJustinSunPrize/awards/pull/670) | JSP-000791: verified three-generator lower bound (partial scope) | `93d3527ead83a384fbbb9bff95291a27fb56e8df` |

They concern, respectively, magic point-configuration certificates, a subpolynomial equidistance counterexample, powerful-number evidence, an infinite tree, factorial differences, another powerful-number submission, and a multiplicative-sequence lower bound. None claims the universal clique edge-partition theorem or an equivalent EGP endpoint. Their unrelated full proof libraries were **not** audited or recompiled, and this screening makes no claim about their validity or completeness.

Issue #663 is a B₃-set catalogue correction, not an EGP submission. It appeared in the issue-search response and is not a missing PR in the above list.

## Focused queries and their limitations

The GitHub PR search connector was queried in repository `TheJustinSunPrize/awards`, with state `all`, newest first, using:

- `"1017"`
- `"Goodman"`
- `"000847"`
- `"EGP"`
- `"edge" "triangle"`

The topic-matching result remained [PR 600](https://github.com/TheJustinSunPrize/awards/pull/600). The broader edge/triangle query also returned older unrelated graph submissions. No post-662 result matched the target.

For transparency, the empty-query search returned only the submitting account's earlier PRs; it was **not** treated as a full repository enumeration. An issue query with `is:pr` returned issue objects, so it likewise was not trusted to enumerate PRs. GitHub web search URLs were restricted, and the ordinary [web PR page](https://github.com/TheJustinSunPrize/awards/pulls) rendered an older list headed by #639. The decisive recent-submission evidence is therefore the successfully retrieved authenticated collection, not those weaker search results.

The previously rate-limited unauthenticated REST request was not retried. The existing authenticated connector is a different successful read-only retrieval channel.

## PR 600: pinned proof closure remains unchanged

A fresh read of the [official PR 600 metadata](https://api.github.com/repos/TheJustinSunPrize/awards/pulls/600) confirmed head commit **`7c0d54e586222713803912b9f2007bf4d4266670`**, unchanged from the earlier source audit, with last recorded update at 08:25:52 UTC.

The previously read complete project proof closure is:

- [Proof.lean](https://github.com/CollinYuanjieRen/awards/blob/7c0d54e586222713803912b9f2007bf4d4266670/submissions/jsp-000847-cyr/Proof.lean), importing Defs and Main;
- [Proof/Defs.lean](https://github.com/CollinYuanjieRen/awards/blob/7c0d54e586222713803912b9f2007bf4d4266670/submissions/jsp-000847-cyr/Proof/Defs.lean), importing Mathlib;
- [Proof/Main.lean](https://github.com/CollinYuanjieRen/awards/blob/7c0d54e586222713803912b9f2007bf4d4266670/submissions/jsp-000847-cyr/Proof/Main.lean), importing Defs.

Its terminal result `sq_div_four_le_f` proves the balanced-bipartite **lower bound**, not the universal upper bound. Its definition requires genuine unique edge ownership, and its other roots prove triangle-free equality, balanced-bipartite counting, and the trivial one-part-per-edge bound. The separate Challenge file has admitted comparator statements and is not imported by the proof. No general EGP upper-bound proof is present in this project closure.

The unchanged local source fingerprints were rechecked:

- Main: `7ab46b423d7a74efc49d35c224890dc9b035757362f7d2b1fcce0334be6940ae`
- Defs: `278488adce6fc4b08c217e3fccab56d847a6b19765eb10acae09366bfc5d8a07`

This refresh did not recompile the old package or its transitive Mathlib dependency library. No matching newer source closure was found to inspect. The earlier source review also identified the lean-genius extra axiom and the ryantuck admitted EGP statements; those fixed historical findings are unchanged, but their entire repositories were not refreshed in this task.

## Assessment boundary

Within the retrieved latest-40 official PR snapshot, the seven post-662 bodies, the focused all-state searches, and the unchanged PR600 proof closure, there is no evidence of a duplicate complete universal EGP formalization. Unindexed work, private work, other repositories, later submissions, and unrelated packages with unstated auxiliary results remain outside this conclusion.

This is an internal Codex source review. The reviewing agent also authored the current package's assembly module; it is not independent third-party or organizer-designated verification. No proof code, toolchain, dependency cache, or public record was modified by this refresh.

