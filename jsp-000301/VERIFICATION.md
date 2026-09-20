# Verification of the JSP-000301 package

Completed on 20 September 2026. These are internal project checks, not an
organizer decision, a third-party human review, or an award determination.

## Checked statements

`Main.lean` proves an explicit consecutive powerful nonsquare pair and the
negation of the entire JSP-000301 yes/no assertion. `Family.lean` proves that
the set of starting values of such pairs is infinite. `Audit.lean` also repeats
the infinite statement with positivity and prime divisibility written directly,
checking its correspondence to the named predicate.

Powerfulness quantifies over every natural prime divisor. Standard `IsSquare`
is used. The infinite conclusion has no additional hypotheses. Its proof uses
induction and a strictly increasing natural-number sequence, not a finite search.

## Actual build and axiom check

The integrated package was built with Lean 4.19.0, compiler commit
`6caaee842e94`, and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
The dependency versions are pinned in `lake-manifest.json`.

| Command | Result | Actual duration |
| --- | --- | --- |
| `lake build` | Exit 0; Main, Family, and Audit freshly built | 52.625 s |
| `lake env lean -DwarningAsError=true Audit.lean` | Exit 0 | 87.641 s |

All 23 named axiom checks reported subsets of `propext`, `Classical.choice`,
and `Quot.sound`. In particular both catalogue endpoints and the infinite-family
endpoint depend only on these standard Lean axioms. No proof placeholder,
custom unproved axiom, or native-computation axiom occurs in the submitted proof.
The finite square-residue lemma uses ordinary `decide`, checked by Lean's kernel.

The source hashes before and after checking were identical:

| Source | SHA-256 |
| --- | --- |
| Main.lean | fa85e05d72b70ef7efc18b6e256d600cf44f2ad1ebd9b35cae8680e27978fbf6 |
| Family.lean | c4b085cdb487a395816a6e61f51dc57f1bbe713ea1cbc7ab1c72c79b032abb73 |
| Audit.lean | d8015d29a6bc1d041407c93bb8f7dcc030791ce07539593a6ad1ce036c6af1c9 |

The [actual result record](verification/integrated-01/result.json),
[build output](verification/integrated-01/build-stdout.txt), and
[axiom output](verification/integrated-01/axioms-stdout.txt) are included.
Both stderr files were empty. Module development checks preceded this integrated
run and are not being presented as independent external verification.

## Reproduction and trust boundary

From this directory, with the specified Lean toolchain installed:

```text
lake exe cache get
lake build
lake env lean -DwarningAsError=true Audit.lean
```

The first command is dependency setup guidance, not a command claimed to have
been run in this verification. Locally, pinned cached dependencies were already
available and were reused. The three project modules were freshly compiled;
Mathlib and its full dependency closure were not freshly rebuilt or separately
replayed in another kernel. This check trusts the ordinary Lean toolchain and
the existing dependency build artifacts. No independent-kernel verification is
claimed for this package.

`python verify.py --label another-check` records the two checking commands and
their actual exits after dependencies are available. Use a fresh label each time.

The same-team semantic review is in [internal-review-c.md](internal-review-c.md).
Historical and formalization provenance, including earlier complete submissions,
is recorded in [README.md](README.md).
