/-
Copyright 2026. Released under the MIT license.

The underlying eight-factor construction is due to Erdős and Rosenfeld;
Jarek Koch previously formalized the same construction with constant 64.
This module supplies sharper bounds for that known construction.
Project initiation and research direction: Gott-L. Lean work: Codex assistance.
-/

import E886Construction
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith

namespace Erdos886

/-- The smallest complementary factor and the smallest selected divisor
strictly bracket the square root. -/
theorem sqrt_bracket {a : ℕ} (ha : 1 ≤ a) :
    (B0 a : ℝ) < Real.sqrt (N a : ℝ) ∧
      Real.sqrt (N a : ℝ) < (A0 a : ℝ) := by
  have hb : (0 : ℝ) < (B0 a : ℝ) := by exact_mod_cast B0_pos ha
  have hab : (B0 a : ℝ) < (A0 a : ℝ) := by exact_mod_cast B0_lt_A0 a
  have hp : (A0 a : ℝ) * (B0 a : ℝ) = (N a : ℝ) := by
    exact_mod_cast A0_mul_B0 a
  have hapos : (0 : ℝ) < (A0 a : ℝ) := lt_trans hb hab
  constructor
  · apply (Real.lt_sqrt hb.le).mpr
    nlinarith [mul_pos hb (sub_pos.mpr hab)]
  · apply (Real.sqrt_lt (by positivity) hapos.le).mpr
    nlinarith [mul_pos hapos (sub_pos.mpr hab)]

/-- A simple lower bound for the fourth root of the eight-factor product. -/
theorem fourth_root_lower (a : ℕ) :
    (a : ℝ) ^ 2 ≤ (N a : ℝ) ^ (1 / 4 : ℝ) := by
  rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num]
  apply (Real.le_rpow_inv_iff_of_pos (sq_nonneg (a : ℝ))
    (by positivity) (show (0 : ℝ) < 4 by norm_num)).mpr
  have h : (a : ℝ) ^ 8 ≤ (N a : ℝ) := by exact_mod_cast pow8_le_N a
  have hr : ((a : ℝ) ^ 2) ^ (4 : ℝ) = ((a : ℝ) ^ 2) ^ (4 : ℕ) :=
    Real.rpow_natCast _ _
  rw [hr]
  convert h using 1; ring

/-- A polynomial gap estimate gives the upper end of the open interval. -/
theorem A3_lt_upper_of_gap {a : ℕ} {C : ℝ} (ha : 1 ≤ a) (hC : 0 ≤ C)
    (hgap : 8 * ((a : ℝ) + 3) * ((a : ℝ) + 5) ≤ C * (a : ℝ) ^ 2) :
    (A3 a : ℝ) < Real.sqrt (N a : ℝ) + C * (N a : ℝ) ^ (1 / 4 : ℝ) := by
  have hg : (B0 a : ℝ) + 8 * ((a : ℝ) + 3) * ((a : ℝ) + 5) = (A3 a : ℝ) := by
    exact_mod_cast B0_add_gap_eq_A3 a
  have hq := mul_le_mul_of_nonneg_left (fourth_root_lower a) hC
  have hb := (sqrt_bracket ha).1
  linarith

/-- The exact constant in the published Erdős–Rosenfeld lower construction. -/
theorem A3_lt_upper16 {a : ℕ} (ha : 10 ≤ a) :
    (A3 a : ℝ) < Real.sqrt (N a : ℝ) + 16 * (N a : ℝ) ^ (1 / 4 : ℝ) := by
  apply A3_lt_upper_of_gap (by omega) (by norm_num)
  have har : (10 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  nlinarith [sq_nonneg ((a : ℝ) - 10)]

/-- The same construction also fits the smaller constant 9 at a later cutoff. -/
theorem A3_lt_upper9 {a : ℕ} (ha : 66 ≤ a) :
    (A3 a : ℝ) < Real.sqrt (N a : ℝ) + 9 * (N a : ℝ) ^ (1 / 4 : ℝ) := by
  apply A3_lt_upper_of_gap (by omega) (by norm_num)
  have har : (66 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
  nlinarith [sq_nonneg ((a : ℝ) - 66)]

end Erdos886
