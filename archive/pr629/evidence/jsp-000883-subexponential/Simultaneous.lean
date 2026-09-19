/-
Copyright 2026. Released under the Apache 2.0 license; see LICENSE.
Original formalization: 56647563 with Codex assistance, TheJustinSunPrize/awards PR601.
Source: https://github.com/56647563/awards/tree/5130380a1d7f3ed00b827c666c79c89e202c3fdc/submissions/jsp-000883
Original mathematical attributions: Ricky Cipollini and pw/erdos1063-upper-bound.
Adaptation: Mathlib 4.19 compatibility. Gott-L directed the project and its
objectives; Codex performed the compatibility implementation and checks.
The original proof is reused under Apache-2.0, not claimed as a new discovery.
-/
import FiniteConstruction
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.BigOperators

namespace Erdos1063
open Finset

theorem same_box_close {Q p u v E : ℕ} (hp : 0 < p) (_hQ : 0 < Q)
    (hsize : p ≤ Q*E) (heq : Q*u/p = Q*v/p) :
    u < v+E ∧ v < u+E := by
  have hu := Nat.mod_add_div (Q*u) p
  have hv := Nat.mod_add_div (Q*v) p
  have hur := Nat.mod_lt (Q*u) hp
  have hvr := Nat.mod_lt (Q*v) hp
  rw [heq] at hu
  have huv : Q*u < Q*v+p := by omega
  have hvu : Q*v < Q*u+p := by omega
  constructor
  · by_contra h
    have hmul := Nat.mul_le_mul_left Q (by omega : v+E ≤ u)
    rw [Nat.mul_add] at hmul
    omega
  · by_contra h
    have hmul := Nat.mul_le_mul_left Q (by omega : u+E ≤ v)
    rw [Nat.mul_add] at hmul
    omega

/-- Integer boxes give a simultaneous approximation with an explicit bound.
This avoids floating-point arithmetic and real-number rounding entirely. -/
theorem simultaneous_boxes (R : Finset ℕ) (S Q E : ℕ) (hQ : 0 < Q)
    (hpos : ∀ p ∈ R, 0 < p) (hsize : ∀ p ∈ R, p ≤ Q*E) :
    ∃ s t : ℕ, s < t ∧ t ≤ Q^R.card ∧
      ∀ p ∈ R, (t*S) % p < (s*S) % p + E ∧
        (s*S) % p < (t*S) % p + E := by
  classical
  let N := Q^R.card
  let box : Fin (N+1) → (R → Fin Q) := fun t p =>
    ⟨Q*((t.val*S) % p.val)/p.val, Nat.div_lt_of_lt_mul (by
      have hmod := Nat.mod_lt (t.val*S) (hpos p.val p.property)
      have hm := Nat.mul_lt_mul_of_pos_left hmod hQ
      simpa [Nat.mul_comm] using hm)⟩
  have hcard : Fintype.card (R → Fin Q) < Fintype.card (Fin (N+1)) := by
    simp [Fintype.card_pi, N]
  obtain ⟨s,t,hne,heq⟩ := Fintype.exists_ne_map_eq_of_card_lt box hcard
  have hclose : ∀ p ∈ R, (t.val*S) % p < (s.val*S) % p + E ∧
      (s.val*S) % p < (t.val*S) % p + E := by
    intro p hp
    have hb := congrArg (fun f => (f ⟨p,hp⟩).val) heq
    exact same_box_close (hpos p hp) hQ (hsize p hp) hb.symm
  have hne' : s.val ≠ t.val := fun h => hne (Fin.ext h)
  rcases lt_or_gt_of_ne hne' with hst | hts
  · exact ⟨s.val,t.val,hst,by have := t.isLt; omega,hclose⟩
  · refine ⟨t.val,s.val,hts,by have := s.isLt; omega,?_⟩
    intro p hp
    exact (hclose p hp).symm

theorem close_residue_carry {p E k u v w : ℕ} (hp : 0 < p)
    (hu : u < p) (hw : w < p) (hsum : v = (u+w) % p)
    (hclose : v < u+E ∧ u < v+E) (hregular : 2*E ≤ k % p) :
    (E+w) % p < k % p := by
  have hkmod := Nat.mod_lt k hp
  have hE : E < p := by omega
  have he := Nat.add_mod_add_ite u w p
  rw [Nat.mod_eq_of_lt hu, Nat.mod_eq_of_lt hw, ← hsum] at he
  by_cases hwrap : p ≤ u+w
  · rw [if_pos hwrap] at he
    have hEp : p ≤ E+w := by omega
    have hrem : E+w-p < p := by omega
    rw [Nat.mod_eq_sub_mod hEp, Nat.mod_eq_of_lt hrem]
    omega
  · rw [if_neg hwrap] at he
    have hrem : E+w < p := by omega
    rw [Nat.mod_eq_of_lt hrem]
    omega

theorem difference_carry {p E k S s t : ℕ} (hp : 0 < p) (hst : s < t)
    (hclose : (t*S) % p < (s*S) % p + E ∧ (s*S) % p < (t*S) % p + E)
    (hregular : 2*E ≤ k % p) : (E+(t-s)*S) % p < k % p := by
  have he : s*S+(t-s)*S = t*S := by
    rw [← Nat.add_mul, Nat.add_sub_of_le (le_of_lt hst)]
  have hsum := Nat.add_mod (s*S) ((t-s)*S) p
  rw [he] at hsum
  have hc := close_residue_carry hp (Nat.mod_lt (s*S) hp)
    (Nat.mod_lt ((t-s)*S) hp) hsum hclose hregular
  have hE : E < p := by have := Nat.mod_lt k hp; omega
  rw [Nat.add_mod E ((t-s)*S), Nat.mod_eq_of_lt hE]
  exact hc

/-- Simultaneous residue conditions with 1 ≤ m ≤ Q^|R|. -/
theorem exists_regular_multiplier (R : Finset ℕ) (S Q E k : ℕ) (hQ : 0 < Q)
    (hpos : ∀ p ∈ R, 0 < p) (hsize : ∀ p ∈ R, p ≤ Q*E)
    (hregular : ∀ p ∈ R, 2*E ≤ k % p) :
    ∃ m : ℕ, 1 ≤ m ∧ m ≤ Q^R.card ∧ ∀ p ∈ R, (E+S*m) % p < k % p := by
  obtain ⟨s,t,hst,ht,hclose⟩ := simultaneous_boxes R S Q E hQ hpos hsize
  refine ⟨t-s, by omega, by omega, ?_⟩
  intro p hp
  simpa [Nat.mul_comm] using difference_carry (hpos p hp) hst
    (hclose p hp) (hregular p hp)

def regularPrimes (E k y : ℕ) : Finset ℕ :=
  {p ∈ constructionPrimes k | y < p ∧ 2*E ≤ k % p}

/-- There is an actual witness below this explicit finite bound; no residue
or local-divisibility assumptions remain. -/
theorem exists_bounded_witness {E k y Q : ℕ} (hk : 2 ≤ k) (hE : E < k)
    (hQ : 0 < Q) (hsize : k ≤ Q*E) (hy : k < (y+1)^2) :
    ∃ n : ℕ, 2*k ≤ n ∧
      (∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧ ∀ i < k, i ≠ i0 → n-i ∣ n.choose k) ∧
      n ≤ E + anchorProduct E k y k.minFac * Q^(regularPrimes E k y).card := by
  have hstar : k.minFac.Prime := Nat.minFac_prime (by omega)
  let R := regularPrimes E k y
  let S := anchorProduct E k y k.minFac
  have hpos : ∀ p ∈ R, 0 < p := by
    intro p hp
    exact (mem_filter.mp (mem_filter.mp hp).1).2.pos
  have hRsize : ∀ p ∈ R, p ≤ Q*E := by
    intro p hp
    have hp' := mem_range.mp (mem_filter.mp (mem_filter.mp hp).1).1
    omega
  have hreg : ∀ p ∈ R, 2*E ≤ k % p := fun p hp => (mem_filter.mp hp).2.2
  obtain ⟨m,hm,hmBound,hmReg⟩ := exists_regular_multiplier R S Q E k hQ hpos hRsize hreg
  have hw := finite_witness hk hE hstar (Nat.minFac_dvd k) hm hy
    (by
      intro p hp hpk hpy hrem
      apply hmReg p
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr (by omega), hp⟩, hpy, hrem⟩)
  refine ⟨E+S*m, hw.1, ⟨E,hE,hw.2⟩, ?_⟩
  exact Nat.add_le_add_left (Nat.mul_le_mul_left S hmBound) E

#print axioms simultaneous_boxes
#print axioms difference_carry
#print axioms exists_regular_multiplier
#print axioms exists_bounded_witness
end Erdos1063

