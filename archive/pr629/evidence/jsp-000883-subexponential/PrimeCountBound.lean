/-
Copyright (c) 2026. Released under the Apache 2.0 license.
Project initiation and research direction: Gott-L.
Proof development, implementation and checks: Codex assistance.

An elementary, deliberately coarse Chebyshev bound. The only prime-product
estimate used is Mathlib's `primorial_le_4_pow` (Patrick Stevens and
Yury Kudryashov). No prime number theorem or new mathematical priority is claimed.
-/
import Mathlib.NumberTheory.Primorial
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open Finset

namespace Erdos1063

/-- The exact number of primes at most k. -/
def primeCount (k : ℕ) : ℕ := ((Finset.range (k + 1)).filter Nat.Prime).card

private theorem sum_log_primes_le (k : ℕ) :
    (∑ p ∈ (Finset.range (k + 1)).filter Nat.Prime, Real.log (p : ℝ)) ≤ 2 * k := by
  have hprod :
      (∏ p ∈ (Finset.range (k + 1)).filter Nat.Prime, (p : ℝ)) = (primorial k : ℝ) := by
    simp only [primorial, Nat.cast_prod]
  have hne : ∀ p ∈ (Finset.range (k + 1)).filter Nat.Prime, (p : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (Finset.mem_filter.mp hp).2.ne_zero
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h
    exact h
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    linarith
  calc
    _ = Real.log (primorial k : ℝ) := by rw [← Real.log_prod _ _ hne, hprod]
    _ ≤ Real.log ((4 : ℝ) ^ k) := by
      apply Real.log_le_log
      · exact_mod_cast primorial_pos k
      · exact_mod_cast primorial_le_4_pow k
    _ ≤ 2 * k := by
      rw [Real.log_pow]
      nlinarith [show (0 : ℝ) ≤ k from Nat.cast_nonneg k]

/-- A multiplicative form of a coarse Chebyshev upper bound, valid for every k.
Using a product bound and splitting at the natural square root avoids all
asymptotic prime-distribution results. -/
theorem primeCount_mul_log_le (k : ℕ) :
    (primeCount k : ℝ) * Real.log k ≤ 6 * k := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  let q := Nat.sqrt k
  let S := (Finset.range (k + 1)).filter Nat.Prime
  let L := S.filter (fun p => p ≤ q)
  let H := S.filter (fun p => ¬ p ≤ q)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hklog : 0 ≤ Real.log (k : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hk)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqSq : (q : ℝ) ^ 2 ≤ k := by exact_mod_cast Nat.sqrt_le' k
  have hlog : Real.log (k : ℝ) ≤ 2 * q := by
    have hlt : (k : ℝ) < ((q : ℝ) + 1) ^ 2 := by
      exact_mod_cast Nat.lt_succ_sqrt' k
    have hlog := Real.log_le_log hkR hlt.le
    rw [Real.log_pow] at hlog
    have hsmall := Real.log_le_sub_one_of_pos (show (0 : ℝ) < q + 1 by positivity)
    norm_num at hlog
    linarith
  have hLcard : L.card ≤ q := by
    have hs : L ⊆ Finset.Icc 1 q := by
      intro p hp
      obtain ⟨hp, hpq⟩ := Finset.mem_filter.mp hp
      have hprime := (Finset.mem_filter.mp hp).2
      exact Finset.mem_Icc.mpr ⟨hprime.one_lt.le, hpq⟩
    simpa only [Nat.card_Icc, Nat.add_sub_cancel] using Finset.card_le_card hs
  have hsmall : (L.card : ℝ) * Real.log k ≤ 2 * k := by
    have hcard : (L.card : ℝ) ≤ q := by exact_mod_cast hLcard
    have ha := mul_le_mul_of_nonneg_right hcard hklog
    have hb := mul_le_mul_of_nonneg_left hlog hq0
    nlinarith
  have hlarge : (H.card : ℝ) * Real.log k ≤ 4 * k := by
    have hpoint : ∀ p ∈ H, Real.log (k : ℝ) ≤ 2 * Real.log (p : ℝ) := by
      intro p hp
      have hpq := (Finset.mem_filter.mp hp).2
      have hsq : (k : ℝ) < (p : ℝ) ^ 2 := by
        exact_mod_cast (Nat.sqrt_lt'.mp (show Nat.sqrt k < p by omega))
      have h := Real.log_le_log hkR hsq.le
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    have hsubset : H ⊆ S := Finset.filter_subset _ _
    have hsum : (∑ p ∈ H, Real.log (p : ℝ)) ≤ ∑ p ∈ S, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p hp _
      exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_lt.le)
    have htotal : (∑ p ∈ S, Real.log (p : ℝ)) ≤ 2 * k := sum_log_primes_le k
    calc
      _ = ∑ p ∈ H, Real.log (k : ℝ) := by simp
      _ ≤ ∑ p ∈ H, 2 * Real.log (p : ℝ) := Finset.sum_le_sum hpoint
      _ = 2 * ∑ p ∈ H, Real.log (p : ℝ) := by rw [Finset.mul_sum]
      _ ≤ 4 * k := by linarith
  have hsplit : L.card + H.card = primeCount k :=
    Finset.filter_card_add_filter_neg_card_eq_card (s := S) (fun p => p ≤ q)
  have hsplitR : (L.card : ℝ) + H.card = primeCount k := by exact_mod_cast hsplit
  nlinarith

#print axioms primeCount_mul_log_le

end Erdos1063
