/-
Copyright 2026. Released under the Apache 2.0 license.

Project concept, objectives, research direction and submission ownership: Gott-L.
Mathematical proof development and Lean implementation: Codex assistance.
This formalizes a known Erdős–Selfridge observation, not a new mathematical result.
-/

import MaxValuation
import OffsetProduct
import Mathlib.Data.Finset.Max

open Finset

namespace Erdos1063

/-- In any positive descending block of length at least two, at least one
entry fails to divide the associated binomial coefficient. -/
theorem exists_exception_of_le {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    ∃ i < k, ¬ (n - i) ∣ n.choose k := by
  have hk0 : k ≠ 0 := by omega
  have hc0 : n.choose k ≠ 0 := (Nat.choose_pos hkn).ne'
  obtain ⟨p, hp, hpk⟩ := Nat.exists_prime_and_dvd (show k ≠ 1 by omega)
  have hpkval : 1 ≤ k.factorization p :=
    (hp.dvd_iff_one_le_factorization hk0).mp hpk
  have hs : (range k).Nonempty := ⟨0, mem_range.mpr (by omega)⟩
  obtain ⟨i, hi, hmax⟩ := exists_max_image (range k)
    (fun j => (n - j).factorization p) hs
  have hik : i < k := mem_range.mp hi
  have hpos : ∀ j ∈ range k, n - j ≠ 0 := by
    intro j hj
    have hjk := mem_range.mp hj
    omega
  have hrest : (∑ j ∈ (range k).erase i, (n - j).factorization p) ≤
      (k - 1).factorial.factorization p := by
    calc
      _ ≤ ∑ j ∈ (range k).erase i, (Nat.dist i j).factorization p := by
        apply sum_le_sum
        intro j hj
        have hji := mem_erase.mp hj
        have hjk := mem_range.mp hji.2
        exact factorization_le_offset_dist hp (by omega) (by omega)
          hji.1.symm (hmax j hji.2)
      _ ≤ _ := sum_factorization_dist_le hik
  have hsum : (n - i).factorization p +
      (∑ j ∈ (range k).erase i, (n - j).factorization p) =
      ∑ j ∈ range k, (n - j).factorization p :=
    add_sum_erase (range k) (fun j => (n - j).factorization p) hi
  have hprod : (n.descFactorial k).factorization p =
      ∑ j ∈ range k, (n - j).factorization p := by
    rw [Nat.descFactorial_eq_prod_range]
    exact factorization_prod_apply hpos
  have hfac : k.factorial.factorization p =
      k.factorization p + (k - 1).factorial.factorization p := by
    conv_lhs => rw [← Nat.mul_factorial_pred hk0]
    rw [Nat.factorization_mul hk0 (Nat.factorial_ne_zero _), Finsupp.add_apply]
  have hchoose : (n.descFactorial k).factorization p =
      k.factorial.factorization p + (n.choose k).factorization p := by
    rw [Nat.descFactorial_eq_factorial_mul_choose,
      Nat.factorization_mul (Nat.factorial_ne_zero _) hc0, Finsupp.add_apply]
  refine ⟨i, hik, ?_⟩
  intro hdvd
  have hle : (n - i).factorization p ≤ (n.choose k).factorization p :=
    (Nat.factorization_le_iff_dvd (hpos i hi) hc0).mpr hdvd p
  omega

/-- The exact `exists_exception` variant in the public Erdős 1063 file;
the stronger theorem above only requires `k ≤ n`. -/
theorem erdos_1063.variants.exists_exception {n k : ℕ}
    (hk : 2 ≤ k) (h : 2 * k ≤ n) :
    ∃ i < k, ¬ (n - i) ∣ n.choose k := by
  exact exists_exception_of_le hk (by omega)

#print axioms exists_exception_of_le
#print axioms erdos_1063.variants.exists_exception

end Erdos1063
