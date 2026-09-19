/-
Copyright (c) 2026. Released under the Apache License, Version 2.0.
Project initiation, conception, objectives, planning and research direction: Gott-L.
Research, formal proof implementation and internal checks: Codex assistance.
Known extension argument: Barreto--Price and Patrick White with Claude;
this is a new implementation, not a mathematical discovery claim.
-/
import E951Weights
import E951Intervals
import E951Series
import E951Sequence

open scoped BigOperators ENNReal
open Set MeasureTheory

namespace E951

def forbiddenUnion {n : ℕ} (a : Fin n → ℝ) (S : ℝ) : Set ℝ :=
  ⋃ u : Fin n → ℕ, ⋃ v : Fin n → ℕ, ⋃ k : ℕ,
    badSet (monomial a u) (monomial a v) S k

theorem forbiddenUnion_volume_le {n : ℕ} (a : Fin n → ℝ) (Z S : ℝ)
    (ha : ∀ i, 1 < a i) (hZ : 0 ≤ Z) (hweight : HasSum (weight a) Z) (hS : 4 ≤ S) :
    volume (forbiddenUnion a S) ≤ ENNReal.ofReal (32 * S * Z ^ 2) := by
  calc
    _ ≤ ∑' u : Fin n → ℕ, volume (⋃ v : Fin n → ℕ, ⋃ k : ℕ,
        badSet (monomial a u) (monomial a v) S k) := measure_iUnion_le _
    _ ≤ ∑' u : Fin n → ℕ, ∑' v : Fin n → ℕ, ∑' k : ℕ,
        volume (badSet (monomial a u) (monomial a v) S k) := by
      apply ENNReal.tsum_le_tsum
      intro u
      calc
        _ ≤ ∑' v : Fin n → ℕ, volume (⋃ k : ℕ,
            badSet (monomial a u) (monomial a v) S k) := measure_iUnion_le _
        _ ≤ _ := ENNReal.tsum_le_tsum (fun v => measure_iUnion_le _)
    _ ≤ ∑' u : Fin n → ℕ, ∑' v : Fin n → ℕ, ∑' k : ℕ,
        ENNReal.ofReal (8 * S ^ 2 * (2 / S) ^ (k + 1) * weight a u * weight a v) := by
      apply ENNReal.tsum_le_tsum
      intro u
      apply ENNReal.tsum_le_tsum
      intro v
      apply ENNReal.tsum_le_tsum
      intro k
      simpa [weight, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        badSet_volume_le (monomial a u) (monomial a v) S k
          (monomial_ge_one ha u) (monomial_ge_one ha v) hS
    _ ≤ _ := weighted_triple_sum_le (weight a) Z S (fun u => (weight_pos ha u).le)
      hZ (tsum_ofReal_weight ha hweight) hS

/-- Above any cutoff a new generator can avoid every cross-power collision. -/
theorem exists_avoiding_above {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 < a i) (B : ℝ) :
    ∃ x : ℝ, B < x ∧ 1 < x ∧ Avoids a x := by
  classical
  obtain ⟨Z, hZ, hweight⟩ := exists_hasSum_weight a ha
  obtain ⟨S, hSbig⟩ := exists_gt (max 4 (max B (32 * Z ^ 2)))
  have hS : 4 ≤ S := (le_max_left _ _).trans hSbig.le
  have hSB : B < S := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hSbig
  have hSZ : 32 * Z ^ 2 < S :=
    lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hSbig
  have hS0 : 0 < S := by linarith
  have hSsq : S ≤ S ^ 2 := by nlinarith
  have hvolume := forbiddenUnion_volume_le a Z S ha hZ.le hweight hS
  have hstrict : ENNReal.ofReal (32 * S * Z ^ 2) < ENNReal.ofReal (S ^ 2) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hS0)).mpr
    nlinarith [mul_lt_mul_of_pos_left hSZ hS0]
  have hex : ∃ x : ℝ, x ∈ Icc (S ^ 2) (2 * S ^ 2) ∧ x ∉ forbiddenUnion a S := by
    by_contra hnone
    have hsub : Icc (S ^ 2) (2 * S ^ 2) ⊆ forbiddenUnion a S := by
      intro x hx
      by_contra hout
      exact hnone ⟨x, hx, hout⟩
    have hmono := measure_mono hsub (μ := volume)
    rw [Real.volume_Icc, show 2 * S ^ 2 - S ^ 2 = S ^ 2 by ring] at hmono
    exact (not_lt_of_ge (hmono.trans hvolume)) hstrict
  obtain ⟨x, hx, hout⟩ := hex
  refine ⟨x, (hSB.trans_le hSsq).trans_le hx.1, ?_, ?_⟩
  · linarith [hx.1]
  · intro u v k
    by_contra hbad
    apply hout
    simp only [forbiddenUnion, mem_iUnion]
    exact ⟨u, v, k, hx, lt_of_not_ge hbad⟩

theorem extension_step : ExtensionStep := by
  intro n a ha hsep B
  obtain ⟨x, hBx, hx, havoid⟩ := exists_avoiding_above a ha B
  exact ⟨x, hBx, hx, separated_snoc a x ha hsep hx.le havoid⟩

/-- Every finite strongly separated prefix extends to a complete infinite sequence. -/
theorem finite_prefix_extension {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 1 < a i) (hmono : StrictMono a) (hsep : Separated a) :
    ∃ b : ℕ → ℝ, StrictMono b ∧ (∀ i, 1 < b i) ∧
      (∀ i : Fin n, b i = a i) ∧ SequenceSeparated b :=
  exists_sequence_extension extension_step a ha hmono hsep

end E951
