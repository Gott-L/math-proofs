# Internal semantic review and fresh replay

Original review documentation, copyright 2026, licensed under CC BY 4.0; see `LICENSE-CONTENT`. The Lean review sources are Apache-2.0.

The seven frozen proof modules establish the stated finite-prefix extension theorem. No mathematical defect or undischarged existence premise was found. For every finite strictly increasing prefix of real numbers greater than one satisfying the strong exponent-vector separation condition, the final theorem constructs an infinite strictly increasing sequence agreeing with the entire prefix and satisfying the same condition for all finitely supported natural exponent vectors.

The reviewer authored `E951Append.lean` and `E951Sequence.lean`. The other five proof modules were authored by other agents. This report records a same-team AI semantic review and a separately executed fresh replay. It is not an external human review, official verification, or an independence claim for the two modules the reviewer wrote.

## Statements checked independently

[`review-a/Audit.lean`](review-a/Audit.lean) contains twelve separately transcribed checks. The final theorem is restated with finite products and `Finsupp.prod` directly, with the custom separation predicates expanded. Its only hypotheses are that the given prefix is strictly increasing, all its entries exceed one, and all distinct finite natural exponent vectors give products at distance at least one.

The result quantifies over every pair of distinct finitely supported exponent vectors on the natural numbers. It preserves each old coordinate exactly. No finite bound on exponents or support size remains. No summability assumption, forbidden-set measure assumption, avoidance witness, or next-step existence premise remains in this endpoint.

The other checks cover:

- The unconditional avoidance theorem above any real cutoff, assuming only that the old generators exceed one, with all old exponent pairs and every positive new exponent represented as `k+1`.
- The complete separated one-step extension theorem, with its products written explicitly.
- Injectivity of both finite and infinite monomial maps under the respective separation assumptions.
- Exact equality between a finitely supported product and its product over a sufficiently long finite prefix.
- Existence of the actual inverse-square-root weight sum, the geometric tail bound, the weighted forbidden-set measure bound, and the full forbidden-union measure bound.
- The empty-prefix case and the fact that the zero exponent vector has product one.

The two injectivity checks specifically exclude an equal-product loophole. The definitions require separation when exponent vectors differ, even if their numerical products were hypothetically equal. Such equality contradicts the lower bound of one. Zero vectors and zero coordinates are included.

## Mathematical chain reviewed

The definitions in `E951Defs.lean` use ordinary finite products and finitely supported products. The weights are exactly the reciprocals of the nonnegative square roots of the finite monomials. Since every generator exceeds one, every monomial is at least one and every weight is positive.

`E951Weights.lean` proves the weight sum by induction on the number of generators. Splitting an exponent vector into its first coordinate and the rest identifies the sum with a product of convergent geometric series, with ratios `1 / sqrt(a i)` strictly between zero and one. The implementation supplies an actual `HasSum` proof and transfers it to the nonnegative extended reals. This argument does not assume that different exponent vectors already give different products. Repeated numerical values merely contribute repeated nonnegative terms to the same convergent indexed sum. For an empty prefix, there is one exponent vector and total weight one.

For generators' monomials `s,t ≥ 1`, `E951Intervals.lean` considers the set of points in `[S²,2S²]` satisfying `|s*x^(k+1)-t| < 1`, where `S ≥ 4`. A proved elementary difference-of-powers inequality bounds the distance between any two such points by `2/(s*(S²)^k)`. Enclosing a nonempty forbidden set in an interval around one of its points gives the outer-measure bound `4/(s*(S²)^k)`. The empty case is handled separately.

Nonemptiness also yields `sqrt(t) ≤ 2*sqrt(s)*(2*S)^(k+1)`. Combining this with the preceding interval bound gives

```text
volume(badSet s t S k)
  ≤ ofReal(8*S²*(2/S)^(k+1)/(sqrt(s)*sqrt(t))).
```

All divisions used in deriving this estimate have proved positive denominators. No differentiability or omitted measurability hypothesis is used: measure monotonicity and countable subadditivity apply through the measure's outer-measure values on sets.

`E951Series.lean` proves that the positive-power tail for `q=2/S ≤ 1/2` is at most `4/S`. The extended-real sums are nonnegative, so their multiplication and reordering do not depend on an unjustified rearrangement of a conditionally convergent real series. With total weight Z, summing the per-set bounds gives `32*S*Z²`.

`E951Extension.lean` takes the union over every pair of old exponent vectors and every natural k. The finite power of the countable natural-number type is countable. Choosing `S > max(4, B, 32*Z²)` makes the proved union bound strictly smaller than the window's measure `S²`. If the whole window lay in the union, measure monotonicity would contradict this strict inequality. A point outside the union therefore exists, exceeds B and one, and avoids every cross-power near-collision. The forbidden inequalities are strict `< 1`, so their negation gives exactly the required weak bound `≥ 1`, including the boundary case.

In the append proof, equal last exponents reduce to separation of the old exponent vectors; unequal last exponents reduce to a positive exponent difference handled by avoidance. Factoring out the common power cannot reduce the distance because the new generator is at least one. The avoidance theorem includes identical old exponent vectors, so the unequal-last-exponent case has no omitted subcase.

The sequence construction chooses each new generator above the sum of the old positive generators and hence above every old entry. Its sequence is defined using stable entries of compatible finite prefixes; no analytic convergence assertion is needed. Any two finite supports fit into a common initial segment. Product equality under restriction is proved, and equality of the restricted vectors would imply equality of the original vectors because both vanish outside that segment. This establishes the strong infinite separation property.

The intermediate `exists_sequence_extension` intentionally takes `ExtensionStep` as an argument. The final `finite_prefix_extension` supplies `extension_step`, whose proof uses the actual weighted measure argument and `separated_snoc`. The raw final check confirms that this intermediate premise is absent from the final statement.

## Verification and trust boundary

The separate replay completed at `2026-09-17T11:43:44.790478+00:00`, recorded in [`review-a/receipt.json`](review-a/receipt.json). All seven source modules were copied byte-for-byte to a fresh directory and compiled in dependency order using Lean 4.19.0, stack setting 65536, and warnings treated as errors. The old project build directory was excluded from the import path. After correcting two elaboration details in the review statements, the audit modules were compiled against the same already successful fresh proof outputs; no proof source was changed or reused from an old project build.

The replay passed all seven proof modules, twelve typed review checks, and 51 named axiom reports: 39 public source declarations and twelve review declarations. This includes the `GoodPrefix` structure and the attributed helper `extendPrefix_old`. Every audited declaration depends only on `propext`, `Classical.choice`, and `Quot.sound`. The audit source is [`review-a/AxiomAudit.lean`](review-a/AxiomAudit.lean). Private helpers are covered through the dependency closures of their audited users.

The primary verifier's separately recorded 38 selected source declarations and six typed checks are a different selection; this review also names `extendPrefix_old` directly. The counts are not substitutes for one another.

All nine dependency repository revisions were checked against the supplied manifest, including Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`. Existing compiled dependency caches and the Lean toolchain were trusted, not rebuilt from their sources. This review does not certify their bootstrap chains. The receipt uses relative source names and records the command settings, outputs, return codes, versions, dependencies, and hashes without local absolute paths or private contact details.

The frozen source hashes were checked again after replay and remained unchanged:

| Source | SHA-256 |
| --- | --- |
| `E951Defs.lean` | `648b8a165ce32b5d6219592cb8c2d87a564efb67b39b45b6d11ed4717ddc0a96` |
| `E951Weights.lean` | `df4d4038b4e8247bc42a049ac91d5a41dafdd232e15c93f80c2a78c6fe533721` |
| `E951Intervals.lean` | `8eb9f238448b01e2def856ae1a4f03caecc3a4607632f6935a5216e450fa6f9b` |
| `E951Append.lean` | `804b4d4d29cfbdfee3a31d6db6eec88d551a155395e78ff33e1b28fa2b14c6c0` |
| `E951Sequence.lean` | `23c3573036aa8751c626911118257f2ebfed225475edca80ce58eb65dda2408c` |
| `E951Series.lean` | `f49fa7eb1e6e026053506c59ff5f257fd2ac2a9c38fe07e31c0231b4a247ee19` |
| `E951Extension.lean` | `550b17561cffeabbeefd078e66e5f8034c876416990201ba77f05121ebec8d6f` |

## Scope of this result

The README and proof outline accurately describe the implemented extension theorem and the proof's use of strong exponent-vector separation. The historical mathematical attribution and limits of access to earlier sources are recorded in `SOURCES.md`; this report does not replace that bounded source audit or assert global priority.

This is a complete proof of the stated known extension theorem. It does not settle the original eventual prime-counting conjecture, certify an optimal short prefix, or establish infinitely many counting violations. Choosing arbitrarily large next generators does not by itself supply any of those conclusions. The catalogue eligibility restriction and the absence of an award entitlement remain as stated in the package documentation. This review is not an official prize decision.
