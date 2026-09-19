/-
Copyright (c) 2026. Released under the Apache License, Version 2.0.
Project initiation, conception, objectives, planning and research direction: Gott-L.
Research, formal proof implementation and internal checks: Codex assistance.
Known extension argument: Barreto--Price and Patrick White with Claude;
this is a new implementation, not a mathematical discovery claim.
-/
import E951Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas

open scoped BigOperators ENNReal

namespace E951

theorem geometric_tail_bound (S : ℝ) (hS : 4 ≤ S) :
    (∑' k : ℕ, ENNReal.ofReal ((2 / S) ^ (k + 1))) ≤ ENNReal.ofReal (4 / S) := by
  have hS0 : 0 < S := by linarith
  have hq0 : 0 ≤ 2 / S := div_nonneg (by norm_num) hS0.le
  have hqhalf : 2 / S ≤ 1 / 2 := (div_le_iff₀ hS0).2 (by linarith)
  have hq1 : 2 / S < 1 := by linarith
  have hsum : HasSum (fun k : ℕ => (2 / S) ^ (k + 1))
      ((2 / S) * (1 - 2 / S)⁻¹) := by
    simpa only [pow_succ'] using (hasSum_geometric_of_lt_one hq0 hq1).mul_left (2 / S)
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg hq0 (k + 1)) hsum.summable,
    hsum.tsum_eq]
  apply ENNReal.ofReal_le_ofReal
  have hden : 0 < 1 - 2 / S := by linarith
  have hinv : (1 - 2 / S)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hden).2 (by linarith)
  calc
    (2 / S) * (1 - 2 / S)⁻¹ ≤ (2 / S) * 2 := mul_le_mul_of_nonneg_left hinv hq0
    _ = 4 / S := by ring

theorem weighted_triple_sum_le {ι : Type*} (w : ι → ℝ) (Z S : ℝ)
    (hw : ∀ u, 0 ≤ w u) (hZ : 0 ≤ Z)
    (hsum : (∑' u, ENNReal.ofReal (w u)) = ENNReal.ofReal Z) (hS : 4 ≤ S) :
    (∑' u, ∑' v, ∑' k : ℕ,
      ENNReal.ofReal (8 * S ^ 2 * (2 / S) ^ (k + 1) * w u * w v)) ≤
      ENNReal.ofReal (32 * S * Z ^ 2) := by
  have hS0 : 0 < S := by linarith
  have hC : 0 ≤ 8 * S ^ 2 := by positivity
  have hq : 0 ≤ 2 / S := by positivity
  have hf : 0 ≤ 4 / S := by positivity
  have heq (u v : ι) (k : ℕ) :
      ENNReal.ofReal (8 * S ^ 2 * (2 / S) ^ (k + 1) * w u * w v) =
      ENNReal.ofReal (8 * S ^ 2) * ENNReal.ofReal (w u) * ENNReal.ofReal (w v) *
        ENNReal.ofReal ((2 / S) ^ (k + 1)) := by
    rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hC (pow_nonneg hq _)) (hw u)),
      ENNReal.ofReal_mul (mul_nonneg hC (pow_nonneg hq _)), ENNReal.ofReal_mul hC]
    ring
  simp_rw [heq, ENNReal.tsum_mul_left]
  calc
    _ ≤ ∑' u, ∑' v, ENNReal.ofReal (8 * S ^ 2) * ENNReal.ofReal (w u) *
        ENNReal.ofReal (w v) * ENNReal.ofReal (4 / S) := by
      apply ENNReal.tsum_le_tsum
      intro u
      apply ENNReal.tsum_le_tsum
      intro v
      exact mul_le_mul_left' (geometric_tail_bound S hS) _
    _ = ENNReal.ofReal (8 * S ^ 2) * ENNReal.ofReal (4 / S) *
        ENNReal.ofReal Z * ENNReal.ofReal Z := by
      calc
        _ = ∑' u, (ENNReal.ofReal (8 * S ^ 2) * ENNReal.ofReal (4 / S) *
            ENNReal.ofReal (w u)) * (∑' v, ENNReal.ofReal (w v)) := by
          apply tsum_congr
          intro u
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro v
          ring
        _ = (ENNReal.ofReal (8 * S ^ 2) * ENNReal.ofReal (4 / S) *
            (∑' v, ENNReal.ofReal (w v))) * (∑' u, ENNReal.ofReal (w u)) := by
          rw [← ENNReal.tsum_mul_left]
          apply tsum_congr
          intro u
          ring
        _ = _ := by rw [hsum]
    _ = ENNReal.ofReal (32 * S * Z ^ 2) := by
      rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul (mul_nonneg hC hf),
        ← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hC hf) hZ)]
      congr 1
      field_simp
      ring

end E951
