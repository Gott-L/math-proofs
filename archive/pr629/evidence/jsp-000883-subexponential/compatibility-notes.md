# Pinned finite-proof reuse and Lean 4.19 adaptation

The finite construction is reused from [56647563's PR 601 source](https://github.com/56647563/awards/tree/5130380a1d7f3ed00b827c666c79c89e202c3fdc/submissions/jsp-000883), fixed commit `5130380a1d7f3ed00b827c666c79c89e202c3fdc`, under Apache-2.0. The original formalization credits 56647563 with Codex assistance and retains the mathematical work of Ricky Cipollini and Patrick White and their stated collaborators. This adaptation retains those attributions and the supplied LICENSE. Gott-L directed this project; Codex performed the compatibility work and checks.

The three original proof bodies were copied from the pinned files. After removing the added provenance header and reversing the changes listed below, a text comparison found exact equality with each saved original:

- `OneCarry.lean`: its first import now selects `CarryCompatibility`.
- `FiniteConstruction.lean`: no body change.
- `Simultaneous.lean`: `ite_eq_left hwrap` and `ite_eq_right hwrap` became the Lean 4.19 names `if_pos hwrap` and `if_neg hwrap`.

The new compatibility module supplies four proved interfaces. Nonvanishing of a binomial coefficient follows from `Nat.choose_pos`; the nonprime factorization lemma wraps its older name. The Kummer formula follows from Mathlib 4.19's existing `Prime.emultiplicity_choose` and the proved link between factorization and p-adic valuation. The bounded prime-power count follows from `p^(v_p(n)) <= n < p^b`, the prime-power divisibility criterion, and the cardinality of an integer interval. No carry theorem is assumed as a new axiom, and no original finite-construction hypothesis or conclusion was weakened.

All four modules compiled successfully in the pinned Lean 4.19 / Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b` environment. The 26 existing named axiom reports emitted by the three original modules used only standard Lean axioms. The final separate replay also checks the compatibility declarations and the assembled new result; its actual results are recorded in [review-a/receipt.json](review-a/receipt.json), with scope and participation disclosed in [internal-review.md](internal-review.md). This adaptation note does not substitute for that verification.

The selective cache request added six artifacts for the actual missing dependencies. Existing dependencies were reused. The shared environment measured 1,552,784,601 bytes (approximately 1.446 GiB), below the 3 GiB bound. No full Mathlib cache or alternate Lean toolchain was downloaded.

[port-metadata.json](port-metadata.json) records the original and adapted hashes and the exact source-comparison result. Reusing this already completed finite proof is distinguished from the new subexponential endpoint; no priority claim is made for the reused construction.
