import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
Growth and residue-class decomposition for a new implementation of the
classical lacunary-difference coloring theorem. This is not new mathematics.
-/

namespace GottL894

theorem iterated_growth (a : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hstep : ∀ k, (1 + ε) * (a k : ℝ) ≤ (a (k + 1) : ℝ))
    (k r : ℕ) : (1 + ε) ^ r * (a k : ℝ) ≤ (a (k + r) : ℝ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    calc
      (1 + ε) ^ (r + 1) * (a k : ℝ) =
          (1 + ε) * ((1 + ε) ^ r * (a k : ℝ)) := by ring
      _ ≤ (1 + ε) * (a (k + r) : ℝ) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      _ ≤ (a ((k + r) + 1) : ℝ) := hstep (k + r)
      _ = (a (k + (r + 1)) : ℝ) := by rw [Nat.add_assoc]

theorem exists_stride (a : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hstep : ∀ k, (1 + ε) * (a k : ℝ) ≤ (a (k + 1) : ℝ)) :
    ∃ r : ℕ, 0 < r ∧ ∀ k, 4 * a k ≤ a (k + r) := by
  obtain ⟨r, hr⟩ := exists_nat_gt (3 / ε)
  have hrε : 3 < (r : ℝ) * ε := (div_lt_iff₀ hε).mp hr
  have hpow : (4 : ℝ) ≤ (1 + ε) ^ r := by
    have hBern := one_add_mul_le_pow (a := ε) (by linarith : -2 ≤ ε) r
    linarith
  have hrpos : 0 < r := by
    by_contra h
    have hrzero : r = 0 := Nat.eq_zero_of_not_pos h
    subst r
    norm_num at hpow
  refine ⟨r, hrpos, fun k => ?_⟩
  have hreal : (4 : ℝ) * (a k : ℝ) ≤ (a (k + r) : ℝ) :=
    (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)).trans
      (iterated_growth a ε hε hstep k r)
  exact_mod_cast hreal

theorem stride_subsequence (a : ℕ → ℕ) (r i : ℕ)
    (hstride : ∀ k, 4 * a k ≤ a (k + r)) (j : ℕ) :
    4 * a (r * j + i) ≤ a (r * (j + 1) + i) := by
  have h := hstride (r * j + i)
  simpa [Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

end GottL894
