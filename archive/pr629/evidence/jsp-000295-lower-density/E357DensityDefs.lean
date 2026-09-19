/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.LiminfLimsup

/-!
Minimal Lean 4.19 compatibility extraction from
FormalConjecturesForMathlib/Data/Set/Density.lean at commit
40e7c98697de6f66b8cbdbf641749ab39ed9c152 of
https://github.com/google-deepmind/formal-conjectures.

The two definitions retain the upstream generic order, ambient-set argument,
strict initial interval, natural cardinalities, real quotient, and liminf.
The additional lemmas expose the exact natural-number/universal-ambient formula.
This file does not assert that a lower density is a full asymptotic density.
-/

namespace Set

/-- The upstream partial density, including its default ambient set. -/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

/-- The upstream lower density, with the same default ambient set. -/
noncomputable def lowerDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : ℝ :=
  Filter.atTop.liminf fun b : β => S.partialDensity A b

theorem partialDensity_nonneg {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : 0 ≤ S.partialDensity A b :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem lowerDensity_nonneg {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) : 0 ≤ S.lowerDensity A := by
  rw [lowerDensity, Filter.liminf_eq]
  exact Real.sSup_nonneg' ⟨0,
    Filter.Eventually.of_forall (fun b => partialDensity_nonneg S A b), le_rfl⟩

theorem ncard_Iio_nat (b : ℕ) : (Iio b).ncard = b := by
  rw [← Finset.coe_range, ncard_coe_Finset, Finset.card_range]

/-- For natural numbers the universal ambient denominator is exactly b. -/
theorem partialDensity_nat_univ (S : Set ℕ) (b : ℕ) :
    S.partialDensity Set.univ b = ((S ∩ Iio b).ncard : ℝ) / (b : ℝ) := by
  simp only [partialDensity, inter_univ, univ_inter, ncard_Iio_nat]

/-- The usual lower natural density formula, proved from the upstream definition. -/
theorem lowerDensity_nat_eq_liminf (S : Set ℕ) :
    S.lowerDensity = Filter.atTop.liminf
      (fun b : ℕ => ((S ∩ Iio b).ncard : ℝ) / (b : ℝ)) := by
  simp only [lowerDensity, partialDensity_nat_univ]

end Set
