/-
Copyright 2026. Released under the Apache 2.0 license.

Elementary dyadic bounds for the known lower-density-zero variant of
Erdős Problem 357. Prepared with Codex assistance; no mathematical
discovery or first-formalization priority is asserted.
-/

import E357Intervals
import Mathlib.Data.Finset.Prod

namespace Erdos357

/-- A layer of positive block lengths and starting indices, in that order. -/
def dyadicBlock (R t : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico (2 ^ t) (2 ^ (t + 1))).product
    (Finset.range (2 ^ (2 * R - t - 1)))

/-- Every layer below `R` has the same cardinality. -/
theorem dyadicBlock_card {R t : ℕ} (ht : t < R) :
    (dyadicBlock R t).card = 2 ^ (2 * R - 1) := by
  rw [dyadicBlock, Finset.product_eq_sprod, Finset.card_product, Nat.card_Ico,
    Finset.card_range]
  have hdiff : 2 ^ (t + 1) - 2 ^ t = 2 ^ t := by
    rw [pow_succ]
    omega
  rw [hdiff, ← pow_add]
  congr 1
  omega

/-- Every block in every layer has positive length. -/
theorem dyadicBlock_length_pos {R t r j : ℕ}
    (hx : (r, j) ∈ dyadicBlock R t) : 0 < r := by
  have hr := (Finset.mem_Ico.mp (Finset.mem_product.mp hx).1).1
  exact (Nat.pow_pos (by decide)).trans_le hr

/-- All block sums in a layer lie below one common bound. -/
theorem dyadicBlock_sum_lt {A : ℕ → ℕ} {C R t r j : ℕ}
    (hc : 0 < C) (ht : t < R) (hlin : ∀ u, A u ≤ C * (u + 1))
    (hx : (r, j) ∈ dyadicBlock R t) :
    blockSum A j r < 2 * C * 2 ^ (2 * R) := by
  have hr : r < 2 ^ (t + 1) :=
    (Finset.mem_Ico.mp (Finset.mem_product.mp hx).1).2
  have hj : j < 2 ^ (2 * R - t - 1) :=
    Finset.mem_range.mp (Finset.mem_product.mp hx).2
  have hexp : (t + 1) + (2 * R - t - 1) = 2 * R := by omega
  have hrj : r * j < 2 ^ (2 * R) := by
    calc
      r * j ≤ 2 ^ (t + 1) * j := Nat.mul_le_mul_right j hr.le
      _ < 2 ^ (t + 1) * 2 ^ (2 * R - t - 1) :=
        Nat.mul_lt_mul_of_pos_left hj (Nat.pow_pos (by decide))
      _ = 2 ^ (2 * R) := by rw [← pow_add, hexp]
  have hrr : r * r < 2 ^ (2 * R) := by
    calc
      r * r < 2 ^ (t + 1) * 2 ^ (t + 1) := Nat.mul_self_lt_mul_self hr
      _ = 2 ^ ((t + 1) + (t + 1)) := (pow_add _ _ _).symm
      _ ≤ 2 ^ (2 * R) := Nat.pow_le_pow_right (by decide) (by omega)
  calc
    blockSum A j r ≤ C * r * (j + r) := blockSum_le_of_linear_bound hlin j r
    _ = C * (r * j + r * r) := by rw [Nat.mul_add, Nat.mul_add]; ac_rfl
    _ < C * (2 ^ (2 * R) + 2 ^ (2 * R)) :=
      Nat.mul_lt_mul_of_pos_left (Nat.add_lt_add hrj hrr) hc
    _ = 2 * C * 2 ^ (2 * R) := by rw [Nat.mul_add, Nat.two_mul C, Nat.add_mul]

/-- Different layers are disjoint because their length intervals are disjoint. -/
theorem dyadicBlock_disjoint (R : ℕ) {t u : ℕ} (h : t ≠ u) :
    Disjoint (dyadicBlock R t) (dyadicBlock R u) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨r, j⟩ hx hy
  have hrt := Finset.mem_Ico.mp (Finset.mem_product.mp hx).1
  have hru := Finset.mem_Ico.mp (Finset.mem_product.mp hy).1
  rcases lt_or_gt_of_ne h with htu | hut
  · have hp : 2 ^ (t + 1) ≤ 2 ^ u := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  · have hp : 2 ^ (u + 1) ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (by omega)
    omega

end Erdos357

#print axioms Erdos357.dyadicBlock_card
#print axioms Erdos357.dyadicBlock_length_pos
#print axioms Erdos357.dyadicBlock_sum_lt
#print axioms Erdos357.dyadicBlock_disjoint
