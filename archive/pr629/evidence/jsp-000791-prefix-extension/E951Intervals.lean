/-
Copyright (c) 2026. Released under the Apache 2.0 license.
Project initiation and research direction: Gott-L.
Formalization, implementation, and checks: Codex assistance.

Elementary outer-measure bounds for the forbidden intervals in the
Erdős 951 extension argument. No mathematical priority claim is made.
-/
import E951Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic.FieldSimp

open MeasureTheory Set

namespace E951

def badSet (s t S : ℝ) (k : ℕ) : Set ℝ :=
  {x | x ∈ Icc (S ^ 2) (2 * S ^ 2) ∧ |s * x ^ (k + 1) - t| < 1}

private theorem pow_difference_lower {A x y : ℝ} (k : ℕ)
    (hA : 0 ≤ A) (hAx : A ≤ x) (hxy : x ≤ y) :
    A ^ k * (y - x) ≤ y ^ (k + 1) - x ^ (k + 1) := by
  have hx : 0 ≤ x := hA.trans hAx
  have hy : 0 ≤ y := hx.trans hxy
  have h₁ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA hAx k)
    (sub_nonneg.mpr hxy)
  have h₂ := mul_nonneg hy (sub_nonneg.mpr (pow_le_pow_left₀ hx hxy k))
  rw [pow_succ, pow_succ]
  nlinarith only [h₁, h₂]

private theorem abs_pow_difference_lower {A x y : ℝ} (k : ℕ)
    (hA : 0 ≤ A) (hAx : A ≤ x) (hAy : A ≤ y) :
    A ^ k * |x - y| ≤ |x ^ (k + 1) - y ^ (k + 1)| := by
  rcases le_total x y with hxy | hyx
  · have h := pow_difference_lower k hA hAx hxy
    have hp := pow_le_pow_left₀ (hA.trans hAx) hxy (k + 1)
    rw [abs_of_nonpos (sub_nonpos.mpr hxy), abs_of_nonpos (sub_nonpos.mpr hp)]
    linarith
  · have h := pow_difference_lower k hA hAy hyx
    have hp := pow_le_pow_left₀ (hA.trans hAy) hyx (k + 1)
    rw [abs_of_nonneg (sub_nonneg.mpr hyx), abs_of_nonneg (sub_nonneg.mpr hp)]
    exact h

theorem badSet_distance_le {s t S x y : ℝ} {k : ℕ}
    (hs : 1 ≤ s) (hS : 4 ≤ S) (hx : x ∈ badSet s t S k)
    (hy : y ∈ badSet s t S k) :
    |x - y| ≤ 2 / (s * (S ^ 2) ^ k) := by
  have hs0 : 0 < s := by linarith
  have hS0 : 0 < S ^ 2 := sq_pos_of_pos (by linarith)
  have hden : 0 < s * (S ^ 2) ^ k := mul_pos hs0 (pow_pos hS0 _)
  have hpow := abs_pow_difference_lower k hS0.le hx.1.1 hy.1.1
  have hdiff : |s * x ^ (k + 1) - s * y ^ (k + 1)| < 2 := by
    have htri := abs_sub_le (s * x ^ (k + 1)) t (s * y ^ (k + 1))
    rw [abs_sub_comm t] at htri
    linarith [hx.2, hy.2]
  have hscale : s * |x ^ (k + 1) - y ^ (k + 1)| < 2 := by
    rw [← mul_sub, abs_mul, abs_of_pos hs0] at hdiff
    exact hdiff
  have hmul := mul_le_mul_of_nonneg_left hpow hs0.le
  apply (le_div_iff₀ hden).mpr
  nlinarith only [hmul, hscale]

/-- Nonempty forbidden sets fit in an interval of the stated length.
The conclusion is an outer-measure bound and requires no measurability premise. -/
theorem badSet_volume_le_basic (s t S : ℝ) (k : ℕ)
    (hs : 1 ≤ s) (hS : 4 ≤ S) :
    volume (badSet s t S k) ≤ ENNReal.ofReal (4 / (s * (S ^ 2) ^ k)) := by
  by_cases hne : (badSet s t S k).Nonempty
  · obtain ⟨x, hx⟩ := hne
    have hsub : badSet s t S k ⊆
        Icc (x - 2 / (s * (S ^ 2) ^ k)) (x + 2 / (s * (S ^ 2) ^ k)) := by
      intro y hy
      have h := badSet_distance_le hs hS hy hx
      obtain ⟨hl, hr⟩ := abs_le.mp h
      exact ⟨by linarith, by linarith⟩
    calc
      _ ≤ volume (Icc (x - 2 / (s * (S ^ 2) ^ k))
          (x + 2 / (s * (S ^ 2) ^ k))) := measure_mono hsub
      _ = ENNReal.ofReal (4 / (s * (S ^ 2) ^ k)) := by
        rw [Real.volume_Icc]
        congr 1
        ring
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp

private theorem sqrt_t_le_of_bad {s t S x : ℝ} {k : ℕ}
    (hs : 1 ≤ s) (hS : 4 ≤ S) (hx : x ∈ badSet s t S k) :
    Real.sqrt t ≤ 2 * Real.sqrt s * (2 * S) ^ (k + 1) := by
  have hs0 : 0 ≤ s := by linarith
  have hS0 : 0 ≤ S := by linarith
  have hx0 : 0 ≤ x := (sq_nonneg S).trans hx.1.1
  have hxbound : x ≤ (2 * S) ^ 2 := by nlinarith [hx.1.2, sq_nonneg S]
  have hpow := pow_le_pow_left₀ hx0 hxbound (k + 1)
  have hswap : ((2 * S) ^ 2) ^ (k + 1) = ((2 * S) ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hswap] at hpow
  have hY : 1 ≤ (2 * S) ^ (k + 1) := one_le_pow₀ (by linarith : 1 ≤ 2 * S)
  have hYsq : 1 ≤ ((2 * S) ^ (k + 1)) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_right hs (sq_nonneg ((2 * S) ^ (k + 1)))
  have hxpow := mul_le_mul_of_nonneg_left hpow hs0
  have hbad := (abs_lt.mp hx.2).1
  have ht : t ≤ 4 * s * ((2 * S) ^ (k + 1)) ^ 2 := by nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ 4 * s * ((2 * S) ^ (k + 1)) ^ 2 := ht
    _ = (2 * Real.sqrt s * (2 * S) ^ (k + 1)) ^ 2 := by
      simp only [mul_pow, Real.sq_sqrt hs0]
      ring

private theorem basic_length_le_weighted {s t S x : ℝ} {k : ℕ}
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hS : 4 ≤ S) (hx : x ∈ badSet s t S k) :
    4 / (s * (S ^ 2) ^ k) ≤
      8 * S ^ 2 * (2 / S) ^ (k + 1) / (Real.sqrt s * Real.sqrt t) := by
  have hs0 : 0 < s := by linarith
  have ht0 : 0 < t := by linarith
  have hS0 : 0 < S := by linarith
  have hden : 0 < s * (S ^ 2) ^ k := by positivity
  have hrootden : 0 < Real.sqrt s * Real.sqrt t := by positivity
  have hroot := sqrt_t_le_of_bad hs hS hx
  have hmul := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg s)
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs0.le
  have hscale : Real.sqrt s * Real.sqrt t ≤ 2 * s * (2 * S) ^ (k + 1) := by
    calc
      _ ≤ Real.sqrt s * (2 * Real.sqrt s * (2 * S) ^ (k + 1)) := hmul
      _ = 2 * (Real.sqrt s) ^ 2 * (2 * S) ^ (k + 1) := by ring
      _ = _ := by rw [hsq]
  have hbase : S ^ 2 * (2 / S) = 2 * S := by
    field_simp [hS0.ne']
    ring
  have hid : (8 * S ^ 2 * (2 / S) ^ (k + 1)) * (s * (S ^ 2) ^ k) =
      8 * s * (2 * S) ^ (k + 1) := by
    calc
      _ = 8 * s * ((S ^ 2) ^ (k + 1) * (2 / S) ^ (k + 1)) := by
        rw [pow_succ (S ^ 2)]
        ring
      _ = 8 * s * (S ^ 2 * (2 / S)) ^ (k + 1) := by rw [mul_pow]
      _ = _ := by rw [hbase]
  apply (div_le_div_iff₀ hden hrootden).mpr
  rw [hid]
  nlinarith only [hscale]

/-- The weighted per-pair outer-measure estimate used in the countable union. -/
theorem badSet_volume_le (s t S : ℝ) (k : ℕ)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hS : 4 ≤ S) :
    volume (badSet s t S k) ≤
      ENNReal.ofReal (8 * S ^ 2 * (2 / S) ^ (k + 1) /
        (Real.sqrt s * Real.sqrt t)) := by
  by_cases hne : (badSet s t S k).Nonempty
  · obtain ⟨x, hx⟩ := hne
    exact (badSet_volume_le_basic s t S k hs hS).trans
      (ENNReal.ofReal_le_ofReal (basic_length_le_weighted hs ht hS hx))
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simp

#print axioms badSet_volume_le_basic
#print axioms badSet_volume_le

end E951
