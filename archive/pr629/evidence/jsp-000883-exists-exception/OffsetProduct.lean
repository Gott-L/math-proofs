/-
Copyright 2026. Released under the Apache 2.0 license.

An independent implementation prepared with Codex assistance.
This elementary offset-product argument supports a formalization of the
known Erdős–Selfridge binomial divisibility observation. No mathematical
discovery or first-formalization priority is asserted.
-/

import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Dist

open Finset

namespace Erdos1063

/-- Pointwise form of the factorization product identity. -/
theorem factorization_prod_apply {α : Type*} {p : ℕ}
    {S : Finset α} {g : α → ℕ} (hS : ∀ x ∈ S, g x ≠ 0) :
    (S.prod g).factorization p = ∑ x ∈ S, (g x).factorization p := by
  rw [Nat.factorization_prod hS, Finsupp.finset_sum_apply]

/-- Distances from the last point of an interval are the factorial factors. -/
theorem prod_dist_range (k : ℕ) :
    (∏ j ∈ range k, Nat.dist k j) = k.factorial := by
  calc
    _ = ∏ j ∈ range k, (k - j) := by
      apply prod_congr rfl
      intro j hj
      exact Nat.dist_eq_sub_of_le_right (Nat.le_of_lt (mem_range.mp hj))
    _ = k.descFactorial k := (Nat.descFactorial_eq_prod_range k k).symm
    _ = k.factorial := Nat.descFactorial_self k

/-- Removing offset `i` leaves distances `1,...,i` on its left and
`1,...,k-1-i` on its right, including the empty side at either endpoint. -/
theorem prod_offset_distances {k i : ℕ} (hi : i < k) :
    (∏ j ∈ (range k).erase i, Nat.dist i j) =
      i.factorial * (k - 1 - i).factorial := by
  induction k generalizing i with
  | zero => omega
  | succ k ih =>
      by_cases hik : i = k
      · subst i
        have hs : (range (k + 1)).erase k = range k := by
          ext j
          simp only [mem_erase, mem_range]
          omega
        rw [hs, prod_dist_range]
        simp
      · have hik' : i < k := by omega
        have hs : (range (k + 1)).erase i = insert k ((range k).erase i) := by
          ext j
          simp only [mem_erase, mem_range, mem_insert]
          omega
        have hnot : k ∉ (range k).erase i := by simp
        rw [hs, prod_insert hnot, ih hik', Nat.dist_eq_sub_of_le hik'.le]
        have hd : k - i = (k - 1 - i) + 1 := by omega
        have hd' : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
        rw [hd', Nat.factorial_succ, hd]
        ac_rfl

/-- The offset-distance product divides the factorial of the interval size
minus one, by the ordinary binomial coefficient identity. -/
theorem prod_offset_distances_dvd {k i : ℕ} (hi : i < k) :
    (∏ j ∈ (range k).erase i, Nat.dist i j) ∣ (k - 1).factorial := by
  rw [prod_offset_distances hi]
  exact Nat.factorial_mul_factorial_dvd_factorial (by omega)

/-- The sum of the prime-factorization exponents of all nonzero offset
distances is bounded by the corresponding factorial exponent. -/
theorem sum_factorization_dist_le {k i p : ℕ} (hi : i < k) :
    (∑ j ∈ (range k).erase i, (Nat.dist i j).factorization p) ≤
      (k - 1).factorial.factorization p := by
  have hn : ∀ j ∈ (range k).erase i, Nat.dist i j ≠ 0 := by
    intro j hj
    have hji : j ≠ i := (mem_erase.mp hj).1
    exact (Nat.dist_pos_of_ne hji.symm).ne'
  rw [← factorization_prod_apply hn]
  exact (Nat.factorization_le_iff_dvd (prod_ne_zero_iff.mpr hn)
    (Nat.factorial_ne_zero _)).mpr (prod_offset_distances_dvd hi) p

#print axioms prod_offset_distances
#print axioms prod_offset_distances_dvd
#print axioms sum_factorization_dist_le

end Erdos1063
