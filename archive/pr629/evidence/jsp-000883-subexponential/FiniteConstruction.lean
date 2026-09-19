/-
Copyright 2026. Released under the Apache 2.0 license; see LICENSE.
Original formalization: 56647563 with Codex assistance, TheJustinSunPrize/awards PR601.
Source: https://github.com/56647563/awards/tree/5130380a1d7f3ed00b827c666c79c89e202c3fdc/submissions/jsp-000883
Original mathematical attributions: Ricky Cipollini and pw/erdos1063-upper-bound.
Adaptation: Mathlib 4.19 compatibility. Gott-L directed the project and its
objectives; Codex performed the compatibility implementation and checks.
The original proof is reused under Apache-2.0, not claimed as a new discovery.
-/
import OneCarry

/-! Finite arithmetic construction from the cited Erdős 1063 prior art.
No asymptotic result is asserted by this module. -/

namespace Erdos1063
open Finset

def depth (p k : ℕ) : ℕ := Nat.log p k
def radius (E k : ℕ) : ℕ := max E (k-1-E)
def offsetDepth (p E k : ℕ) : ℕ := Nat.log p (radius E k)
def lowCarries (p E k : ℕ) : ℕ :=
  #{a ∈ Ico 1 (depth p k + 1) | E % p^a < k % p^a}
def deficit (p E k : ℕ) : ℕ := offsetDepth p E k - lowCarries p E k

theorem small_prime_from_depth {p E x k i : ℕ} (hp : p.Prime)
    (hkn : k ≤ E+x) (hE : E < k) (hi : i < k) (hne : i ≠ E)
    (hd : p^(depth p k + deficit p E k) ∣ x) :
    (E+x-i).factorization p ≤ ((E+x).choose k).factorization p := by
  apply small_prime_anchor (A := depth p k) (T := offsetDepth p E k)
    hp hkn hE hi hne
  · exact Nat.lt_pow_succ_log_self hp.one_lt k
  · exact Nat.log_mono_right (by dsimp [radius]; omega)
  · exact lt_of_le_of_lt (le_max_left _ _)
      (Nat.lt_pow_succ_log_self hp.one_lt (radius E k))
  · exact lt_of_le_of_lt (le_max_right _ _)
      (Nat.lt_pow_succ_log_self hp.one_lt (radius E k))
  · exact hd

/-- A prime divisor of k always has a missing first carry; it can be chosen
as the failure prime without searching divisors of k * choose(k-1,E). -/
theorem prime_divisor_deficit {p E k : ℕ} (hp : p.Prime) (hk : 0 < k)
    (hpk : p ∣ k) : lowCarries p E k < depth p k := by
  have hp_le : p ≤ k := Nat.le_of_dvd hk hpk
  have hA : 1 ≤ depth p k := Nat.le_log_of_pow_le hp.one_lt (by simpa using hp_le)
  have hs : {a ∈ Ico 1 (depth p k + 1) | E % p^a < k % p^a} ⊆
      Ico 2 (depth p k + 1) := by
    intro a ha
    obtain ⟨ha, hc⟩ := mem_filter.mp ha
    have ha' := mem_Ico.mp ha
    have hne : a ≠ 1 := by
      intro he
      simp [he, Nat.mod_eq_zero_of_dvd hpk] at hc
    exact mem_Ico.mpr ⟨by omega, ha'.2⟩
  have hc := card_le_card hs
  rw [Nat.card_Ico] at hc
  change lowCarries p E k ≤ depth p k + 1 - 2 at hc
  omega

theorem center_fails_at_prime_divisor {p E x k : ℕ} (hp : p.Prime)
    (hkn : k ≤ E+x) (hE : E < k) (hx : x ≠ 0) (hpk : p ∣ k)
    (hd : p^(depth p k + 1) ∣ x) : ¬ x ∣ (E+x).choose k := by
  exact center_fails hp hkn hE hx (Nat.lt_pow_succ_log_self hp.one_lt k) hd
    (prime_divisor_deficit hp (by omega) hpk)

/-- Combine all prime-local checks into actual divisibility. -/
theorem dvd_choose_of_local {n k i : ℕ} (hkn : k ≤ n) (hi : i < k)
    (hlocal : ∀ p, p.Prime → p ≤ k →
      (n-i).factorization p ≤ (n.choose k).factorization p) : n-i ∣ n.choose k := by
  apply (Nat.factorization_le_iff_dvd (by omega : n-i ≠ 0)
    (Nat.choose_ne_zero hkn)).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hpk : p ≤ k
    · exact hlocal p hp hpk
    · exact large_prime_automatic hp hkn hi (by omega)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

def constructionPrimes (k : ℕ) : Finset ℕ := {p ∈ range (k+1) | p.Prime}
def anchorExponent (p E k y : ℕ) : ℕ :=
  if p ≤ y then depth p k + deficit p E k else if k % p < 2*E then 2 else 0

/-- The harmless factor 2k ensures the window starts far enough out, without
needing an asymptotic lower bound on the product of small primes. -/
def anchorProduct (E k y pstar : ℕ) : ℕ :=
  2*k * (∏ p ∈ constructionPrimes k, p ^ anchorExponent p E k y) *
    pstar ^ (depth pstar k + 1)

theorem anchorProduct_ge {E k y pstar : ℕ} (hstar : pstar.Prime) :
    2*k ≤ anchorProduct E k y pstar := by
  have hprod : 0 < ∏ p ∈ constructionPrimes k, p ^ anchorExponent p E k y := by
    apply Nat.pos_of_ne_zero
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    exact pow_ne_zero _ (mem_filter.mp hp).2.ne_zero
  have hpow : 0 < pstar ^ (depth pstar k + 1) := pow_pos hstar.pos _
  unfold anchorProduct
  exact le_trans (Nat.le_mul_of_pos_right _ hprod) (Nat.le_mul_of_pos_right _ hpow)

theorem anchor_divides_product {p E k y pstar : ℕ} (hp : p.Prime) (hpk : p ≤ k) :
    p ^ anchorExponent p E k y ∣ anchorProduct E k y pstar := by
  have hmem : p ∈ constructionPrimes k := mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩
  have hd : p ^ anchorExponent p E k y ∣
      ∏ q ∈ constructionPrimes k, q ^ anchorExponent q E k y :=
    dvd_prod_of_mem _ hmem
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hd (2*k)) _

theorem failure_power_divides_product {E k y pstar : ℕ} :
    pstar^(depth pstar k+1) ∣ anchorProduct E k y pstar := dvd_mul_left _ _

/-- Complete finite correctness statement: once the regular-prime residues are
supplied, this explicit product yields exactly one failing coordinate. -/
theorem finite_witness {E k y pstar m : ℕ} (_hk : 2 ≤ k) (hE : E < k)
    (hstar : pstar.Prime) (hstarDiv : pstar ∣ k) (hm : 1 ≤ m)
    (hy : k < (y+1)^2)
    (hregular : ∀ p, p.Prime → p ≤ k → y < p → 2*E ≤ k % p →
      (E + anchorProduct E k y pstar * m) % p < k % p) :
    let n := E + anchorProduct E k y pstar * m
    2*k ≤ n ∧ ¬ (n-E) ∣ n.choose k ∧
      ∀ i < k, i ≠ E → n-i ∣ n.choose k := by
  let S := anchorProduct E k y pstar
  have hS : 2*k ≤ S := anchorProduct_ge hstar
  have hSm : 2*k ≤ S*m := by nlinarith
  have hkn : k ≤ E+S*m := by omega
  have hx : S*m ≠ 0 := by omega
  change 2*k ≤ E+S*m ∧ ¬ (E+S*m-E) ∣ (E+S*m).choose k ∧ _
  refine ⟨by omega, ?_, ?_⟩
  · rw [Nat.add_sub_cancel_left]
    exact center_fails_at_prime_divisor hstar hkn hE hx hstarDiv
      (dvd_mul_of_dvd_left failure_power_divides_product m)
  · intro i hi hne
    apply dvd_choose_of_local hkn hi
    intro p hp hpk
    have hd := dvd_mul_of_dvd_left
      (anchor_divides_product (E := E) (y := y) (pstar := pstar) hp hpk) m
    by_cases hpy : p ≤ y
    · apply small_prime_from_depth hp hkn hE hi hne
      simpa [anchorExponent, hpy, S] using hd
    · have hkp2 : k < p^2 := by
        have hpy' : y+1 ≤ p := by omega
        nlinarith
      by_cases hpex : k % p < 2*E
      · apply exceptional_large_prime hp hkn hE hi hne hkp2
        simpa [anchorExponent, hpy, hpex, S] using hd
      · exact one_carry hp hkn hi hkp2 (hregular p hp hpk (by omega) (by omega))

#print axioms small_prime_from_depth
#print axioms prime_divisor_deficit
#print axioms center_fails_at_prime_divisor
#print axioms dvd_choose_of_local
#print axioms finite_witness
end Erdos1063

