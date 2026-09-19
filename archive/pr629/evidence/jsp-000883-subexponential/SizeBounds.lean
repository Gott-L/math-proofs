/-
Adapted from 56647563/awards PR601, commit 5130380a1d7f3ed00b827c666c79c89e202c3fdc,
submissions/jsp-000883/SizeBounds.lean, released under Apache-2.0.
Original formalization: 56647563 with Codex assistance.
Mathematical sources: Patrick White and Ricky Cipollini, with their stated AI collaborators.
Modifications: Mathlib 4.19 compatibility; exact finite prime-count representation.
Gott-L: project initiation, objectives, planning and research direction.
Codex assistance: adaptation, proof extension and checks.
-/
import Simultaneous
import PrimeCountBound

set_option warningAsError true

namespace Erdos1063
open Finset

/-- A deliberately coarse count sufficient for a strict improvement over the
LCM benchmark. Split by the quotient k/p and encode the low-quotient part by
(quotient, remainder). No prime distribution estimate is needed here. -/
theorem small_remainder_count (k E M : ℕ) :
    #{p ∈ Icc 1 k | k % p < 2*E} ≤ 2*E*M + k/(M+1) := by
  let X := {p ∈ Icc 1 k | k % p < 2*E}
  let L := {p ∈ X | k/p ≤ M}
  let H := {p ∈ X | ¬ k/p ≤ M}
  have hL : L.card ≤ 2*E*M := by
    have hb : L.card ≤ ((Icc 1 M) ×ˢ (range (2*E))).card := by
      apply card_le_card_of_injOn (fun p => (k/p,k%p))
      · intro p hp
        obtain ⟨hp,hq⟩ := mem_filter.mp hp
        obtain ⟨hp,hr⟩ := mem_filter.mp hp
        obtain ⟨hp1,hpk⟩ := mem_Icc.mp hp
        exact mem_product.mpr ⟨mem_Icc.mpr ⟨Nat.div_pos hpk (by omega),hq⟩,
          mem_range.mpr hr⟩
      · intro p hp q hq heq
        have hp' := mem_Icc.mp (mem_filter.mp (mem_filter.mp hp).1).1
        have hq' := mem_Icc.mp (mem_filter.mp (mem_filter.mp hq).1).1
        have he1 := congrArg Prod.fst heq
        have he2 := congrArg Prod.snd heq
        have hpdiv : 0 < k/p := Nat.div_pos hp'.2 (by omega)
        have heP := Nat.div_add_mod k p
        have heQ := Nat.div_add_mod k q
        dsimp at he1 he2
        rw [← he1, ← he2] at heQ
        have hmul : p*(k/p) = q*(k/p) := by omega
        exact Nat.eq_of_mul_eq_mul_right hpdiv hmul
    simpa [Nat.card_Icc, Nat.mul_comm] using hb
  have hH : H.card ≤ k/(M+1) := by
    have hs : H ⊆ Icc 1 (k/(M+1)) := by
      intro p hp
      obtain ⟨hp,hq⟩ := mem_filter.mp hp
      have hp' := mem_Icc.mp (mem_filter.mp hp).1
      apply mem_Icc.mpr
      refine ⟨hp'.1, ?_⟩
      have hdiv : (M+1)*p ≤ k :=
        (Nat.le_div_iff_mul_le (by omega : 0 < p)).mp (by omega)
      exact (Nat.le_div_iff_mul_le (by omega : 0 < M+1)).mpr (by simpa [Nat.mul_comm] using hdiv)
    have := card_le_card hs
    simpa [Nat.card_Icc] using this
  have he := filter_card_add_filter_neg_card_eq_card (s := X) (fun p => k/p ≤ M)
  change L.card + H.card = X.card at he
  change X.card ≤ _
  omega

theorem active_prime_count {E k y M : ℕ} :
    #{p ∈ constructionPrimes k | p ≤ y ∨ k % p < 2*E} ≤
      y + (2*E*M + k/(M+1)) := by
  have hs : {p ∈ constructionPrimes k | p ≤ y ∨ k % p < 2*E} ⊆
      Icc 1 y ∪ {p ∈ Icc 1 k | k % p < 2*E} := by
    intro p hp
    obtain ⟨hp,hactive⟩ := mem_filter.mp hp
    obtain ⟨hpk,hprime⟩ := mem_filter.mp hp
    have hpk' := mem_range.mp hpk
    have hp1 := hprime.one_lt
    rcases hactive with hpy | hrem
    · exact mem_union_left _ (mem_Icc.mpr ⟨by omega,hpy⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega,by omega⟩,hrem⟩)
  have hcard := le_trans (card_le_card hs) (card_union_le _ _)
  have hx := small_remainder_count k E M
  rw [Nat.card_Icc] at hcard
  omega

theorem anchor_factor_le {p E k y : ℕ} (hp : p.Prime) (hpk : p ≤ k)
    (hE : E < k) :
    p^anchorExponent p E k y ≤ if p ≤ y ∨ k % p < 2*E then k^2 else 1 := by
  have hA : p^depth p k ≤ k := Nat.pow_log_le_self p (by omega)
  have hT : offsetDepth p E k ≤ depth p k :=
    Nat.log_mono_right (by dsimp [radius]; omega)
  have hH : deficit p E k ≤ depth p k := by unfold deficit; omega
  by_cases hpy : p ≤ y
  · simp only [anchorExponent, hpy, ite_true, true_or]
    calc
      p^(depth p k + deficit p E k) ≤ p^(depth p k * 2) :=
        Nat.pow_le_pow_right hp.pos (by omega)
      _ = (p^depth p k)^2 := pow_mul _ _ _
      _ ≤ k^2 := Nat.pow_le_pow_left hA 2
  · by_cases hrem : k % p < 2*E
    · simp only [anchorExponent,hpy,hrem,ite_false,ite_true,false_or]
      exact Nat.pow_le_pow_left hpk 2
    · simp [anchorExponent,hpy,hrem]

/-- A coarse polynomial-exponent bound on the anchor product. It is adequate
for the final asymptotic comparison and avoids sharper unpublished estimates. -/
theorem anchorProduct_le {E k y pstar M : ℕ} (hk : 1 ≤ k) (hE : E < k)
    (_hstar : pstar.Prime) (hstarDiv : pstar ∣ k) :
    anchorProduct E k y pstar ≤ 2*k^(3 + 2*(y + (2*E*M+k/(M+1)))) := by
  let C := y + (2*E*M+k/(M+1))
  let R := constructionPrimes k
  let P := fun p => p ≤ y ∨ k % p < 2*E
  have hprod : (∏ p ∈ R, p^anchorExponent p E k y) ≤ (k^2)^C := by
    calc
      (∏ p ∈ R, p^anchorExponent p E k y) ≤ ∏ p ∈ R, if P p then k^2 else 1 := by
        apply Finset.prod_le_prod
        · intro p hp
          exact Nat.zero_le _
        · intro p hp
          obtain ⟨hpk,hprime⟩ := mem_filter.mp hp
          exact anchor_factor_le hprime (by have := mem_range.mp hpk; omega) hE
      _ = (k^2)^({p ∈ R | P p}.card) := by
        rw [← prod_filter]
        simp
      _ ≤ (k^2)^C := Nat.pow_le_pow_right (by positivity) active_prime_count
  have hp_le : pstar ≤ k := Nat.le_of_dvd (by omega) hstarDiv
  have hA : pstar^depth pstar k ≤ k := Nat.pow_log_le_self pstar (by omega)
  have hpow : pstar^(depth pstar k+1) ≤ k^2 := by
    rw [pow_succ,pow_two]
    exact Nat.mul_le_mul hA hp_le
  unfold anchorProduct
  calc
    _ ≤ 2*k*(k^2)^C*k^2 := Nat.mul_le_mul (Nat.mul_le_mul_left _ hprod) hpow
    _ = 2*k^(3+2*C) := by ring

theorem regular_card_le (E k y : ℕ) : (regularPrimes E k y).card ≤ primeCount k := by
  change ({p ∈ constructionPrimes k | y < p ∧ 2*E ≤ k % p}).card ≤
    (constructionPrimes k).card
  exact card_filter_le _ _

theorem exists_coarse_bounded_witness {E k y Q M : ℕ} (hk : 2 ≤ k) (hE : E < k)
    (hQ : 0 < Q) (hsize : k ≤ Q*E) (hy : k < (y+1)^2) :
    ∃ n : ℕ, 2*k ≤ n ∧
      (∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧ ∀ i < k, i ≠ i0 → n-i ∣ n.choose k) ∧
      n ≤ 4*k^(3+2*(y+(2*E*M+k/(M+1)))) * Q^primeCount k := by
  obtain ⟨n,hn,hw,hb⟩ := exists_bounded_witness hk hE hQ hsize hy
  refine ⟨n,hn,hw,?_⟩
  let S := anchorProduct E k y k.minFac
  let B := 3+2*(y+(2*E*M+k/(M+1)))
  have hstar := Nat.minFac_prime (by omega : k ≠ 1)
  have hSb : S ≤ 2*k^B := anchorProduct_le (by omega) hE hstar (Nat.minFac_dvd k)
  have hSge : 2*k ≤ S := anchorProduct_ge hstar
  have hq : Q^(regularPrimes E k y).card ≤ Q^primeCount k :=
    Nat.pow_le_pow_right hQ (regular_card_le E k y)
  have hq1 : 1 ≤ Q^primeCount k := Nat.one_le_pow _ _ hQ
  have hEbound : E ≤ S*Q^primeCount k := by nlinarith
  have hbb : n ≤ E+S*Q^primeCount k :=
    le_trans hb (Nat.add_le_add_left (Nat.mul_le_mul_left S hq) E)
  have hprod := Nat.mul_le_mul_right (Q^primeCount k) hSb
  change n ≤ 4*k^B*Q^primeCount k
  nlinarith

#print axioms small_remainder_count
#print axioms anchorProduct_le
#print axioms exists_coarse_bounded_witness
end Erdos1063
