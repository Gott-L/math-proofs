/-
Copyright 2026. Released under the Apache 2.0 license.

An independent implementation prepared with Codex assistance. This is the
elementary density-to-growth step in the known lower-density result recorded
by Paul Erdős in Problems and results on combinatorial number theory III
(1977), p. 70. No mathematical discovery or first-formalization claim is made.
The density definitions are imported from the separately attributed
compatibility module E357DensityDefs.
-/

import E357DensityDefs
import Mathlib.Tactic.Linarith
import Mathlib.Order.WellFounded

namespace Erdos357

/-- A strictly increasing enumeration has exactly `n` range elements below
its `n`th value, using zero-based indexing. -/
theorem count_range_Iio_apply (A : ℕ → ℕ) (hMono : StrictMono A) (n : ℕ) :
    ((Set.range A) ∩ Set.Iio (A n)).ncard = n := by
  have hset : (Set.range A) ∩ Set.Iio (A n) = A '' Set.Iio n := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_Iio, Set.mem_image]
    constructor
    · rintro ⟨⟨m, rfl⟩, hm⟩
      exact ⟨m, hMono.lt_iff_lt.mp hm, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, rfl⟩, hMono hm⟩
  rw [hset, Set.ncard_image_of_injective _ hMono.injective, Set.ncard_Iio_nat]

/-- Positive lower density forces a uniform linear upper bound for a
strictly increasing enumeration. No existence of a density limit is assumed. -/
theorem exists_linear_bound_of_lowerDensity_pos (A : ℕ → ℕ)
    (hMono : StrictMono A) (hDensity : 0 < (Set.range A).lowerDensity) :
    ∃ C : ℕ, 0 < C ∧ ∀ n, A n ≤ C * (n + 1) := by
  let δ : ℝ := (Set.range A).lowerDensity / 2
  have hδ : 0 < δ := half_pos hDensity
  have hδlt : δ < (Set.range A).lowerDensity := by
    dsimp [δ]
    linarith
  have hevent : ∀ᶠ x in Filter.atTop, δ < (Set.range A).partialDensity Set.univ x := by
    exact Filter.eventually_lt_of_lt_liminf hδlt
      (Filter.isBoundedUnder_of ⟨0, fun x => Set.partialDensity_nonneg _ _ x⟩)
  obtain ⟨M0, hM0⟩ := Filter.eventually_atTop.mp hevent
  obtain ⟨D, hD⟩ := exists_nat_ge (1 / δ)
  let M : ℕ := M0 + 1
  refine ⟨D + A M + 1, by omega, ?_⟩
  intro n
  by_cases hn : n < M
  · have hAn : A n ≤ A M := hMono.monotone (Nat.le_of_lt hn)
    calc
      A n ≤ D + A M + 1 := by omega
      _ ≤ (D + A M + 1) * (n + 1) := by
        calc
          D + A M + 1 = (D + A M + 1) * 1 := by omega
          _ ≤ (D + A M + 1) * (n + 1) := Nat.mul_le_mul_left _ (by omega)
  · have hnM : M ≤ n := by omega
    have hnpos : 0 < n := by dsimp [M] at hnM; omega
    have hAn : n ≤ A n := hMono.id_le n
    have hAnpos : (0 : ℝ) < A n := by exact_mod_cast (lt_of_lt_of_le hnpos hAn)
    have hpartial := hM0 (A n) (by dsimp [M] at hnM; omega)
    rw [Set.partialDensity_nat_univ, count_range_Iio_apply A hMono n] at hpartial
    have hprod : δ * (A n : ℝ) < (n : ℝ) := (lt_div_iff₀ hAnpos).mp hpartial
    have hlinear : (A n : ℝ) ≤ (D : ℝ) * n := by
      calc
        (A n : ℝ) ≤ (n : ℝ) / δ := (le_div_iff₀ hδ).mpr (by linarith)
        _ = (n : ℝ) * (1 / δ) := by ring
        _ ≤ (n : ℝ) * D := mul_le_mul_of_nonneg_left hD (Nat.cast_nonneg n)
        _ = (D : ℝ) * n := mul_comm _ _
    have hlinearNat : A n ≤ D * n := by exact_mod_cast hlinear
    exact hlinearNat.trans (Nat.mul_le_mul (by omega) (by omega))

end Erdos357
