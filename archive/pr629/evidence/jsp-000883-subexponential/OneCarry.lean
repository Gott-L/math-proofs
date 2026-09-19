/-
Copyright 2026. Released under the Apache 2.0 license; see LICENSE.
Original formalization: 56647563 with Codex assistance, TheJustinSunPrize/awards PR601.
Source: https://github.com/56647563/awards/tree/5130380a1d7f3ed00b827c666c79c89e202c3fdc/submissions/jsp-000883
Original mathematical attributions: Ricky Cipollini and pw/erdos1063-upper-bound.
Adaptation: Mathlib 4.19 compatibility. Gott-L directed the project and its
objectives; Codex performed the compatibility implementation and checks.
The original proof is reused under Apache-2.0, not claimed as a new discovery.
-/
import CarryCompatibility

/-!
One-carry arithmetic lemma for the existing subexponential upper-bound constructions
for Erdős 1063 (JSP 883). Mathematical prior art: Ricky Cipollini's July 2026
manuscript and https://github.com/pw/erdos1063-upper-bound.
This file does not prove the full construction or its asymptotic bound.
-/

namespace Erdos1063
open Finset

theorem carry_of_mod_lt {n k q : ℕ} (hkn : k ≤ n)
    (h : n % q < k % q) : q ≤ k % q + (n-k) % q := by
  by_contra hc
  have hs : k + (n-k) = n := Nat.add_sub_of_le hkn
  have he := Nat.add_mod k (n-k) q
  rw [hs, Nat.mod_eq_of_lt (by omega : k % q + (n-k) % q < q)] at he
  omega

/-- When `p² > k`, a carry in the units column pays for every power of `p`
dividing any of the `k` consecutive numerator factors. -/
theorem one_carry {p n k i : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hi : i < k) (hsmall : k < p^2) (hcarry : n % p < k % p) :
    (n-i).factorization p ≤ (n.choose k).factorization p := by
  let b := Nat.log p n + 1
  have hn : n < p^b := Nat.lt_pow_succ_log_self hp.one_lt n
  rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega : 0 < n-i)
      (lt_of_le_of_lt (Nat.sub_le n i) hn),
    Nat.factorization_choose (b := b) hp hkn (by dsimp [b]; omega)]
  apply Finset.card_le_card
  intro a ha
  obtain ⟨ha, hd⟩ := Finset.mem_filter.mp ha
  apply Finset.mem_filter.mpr
  refine ⟨ha, carry_of_mod_lt hkn ?_⟩
  have ha1 : 1 ≤ a := (Finset.mem_Ico.mp ha).1
  by_cases he : a = 1
  · simpa [he] using hcarry
  · have ha2 : 2 ≤ a := by omega
    have hkq : k < p^a := lt_of_lt_of_le hsmall (Nat.pow_le_pow_right hp.pos ha2)
    have hiq : i < p^a := lt_trans hi hkq
    have hni : (n-i) + i = n := Nat.sub_add_cancel (by omega)
    have hm : n % p^a = i := by
      rw [← hni, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, zero_add,
        Nat.mod_eq_of_lt hiq, Nat.mod_eq_of_lt hiq]
    rw [hm, Nat.mod_eq_of_lt hkq]
    exact hi

/-- Divisibility form: every prime power in a numerator factor is absorbed
by the binomial coefficient under the one-carry hypotheses. -/
theorem prime_power_dvd_choose {p n k i a : ℕ} (hp : p.Prime) (hkn : k ≤ n)
    (hi : i < k) (hsmall : k < p^2) (hcarry : n % p < k % p)
    (hd : p^a ∣ n-i) : p^a ∣ n.choose k := by
  apply (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hkn)).mpr
  exact le_trans ((hp.pow_dvd_iff_le_factorization (by omega : n-i ≠ 0)).mp hd)
    (one_carry hp hkn hi hsmall hcarry)

/-- Powers larger than the window length automatically give a carry whenever
they divide a numerator factor. -/
theorem high_power_carry {n k i q : ℕ} (hkn : k ≤ n) (hi : i < k)
    (hkq : k < q) (hd : q ∣ n-i) : q ≤ k % q + (n-k) % q := by
  apply carry_of_mod_lt hkn
  have hiq : i < q := lt_trans hi hkq
  have hni : (n-i) + i = n := Nat.sub_add_cancel (by omega)
  have hm : n % q = i := by
    rw [← hni, Nat.add_mod, Nat.mod_eq_zero_of_dvd hd, zero_add,
      Nat.mod_eq_of_lt hiq, Nat.mod_eq_of_lt hiq]
  rw [hm, Nat.mod_eq_of_lt hkq]
  exact hi

private theorem split_count (P : ℕ → Prop) [DecidablePred P]
    {A b : ℕ} (hab : A+1 ≤ b) :
    #{a ∈ Ico 1 b | P a} =
      #{a ∈ Ico 1 (A+1) | P a} + #{a ∈ Ico (A+1) b | P a} := by
  rw [← Ico_union_Ico_eq_Ico (by omega : 1 ≤ A+1) hab, filter_union]
  apply card_union_of_disjoint
  exact (Ico_disjoint_Ico_consecutive 1 (A+1) b).mono
    (filter_subset _ _) (filter_subset _ _)

/-- Truncated covering: only prime powers up to a chosen cutoff require
explicit control. Above it, divisibility automatically supplies the carries.
The low-level premise compares counts, allowing surplus at one level to pay
for a missing carry at another level of the same prime. -/
theorem truncated_covering {p n k i A : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hi : i < k) (hcut : k < p^(A+1))
    (hlow : #{a ∈ Ico 1 (A+1) | p^a ∣ n-i} ≤
      #{a ∈ Ico 1 (A+1) | p^a ≤ k % p^a + (n-k) % p^a}) :
    (n-i).factorization p ≤ (n.choose k).factorization p := by
  let b := max (Nat.log p n + 1) (A+1)
  have hab : A+1 ≤ b := le_max_right _ _
  have hlog : Nat.log p n < b := lt_of_lt_of_le (by omega) (le_max_left _ _)
  have hn : n < p^b := Nat.lt_pow_of_log_lt hp.one_lt hlog
  rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega : 0 < n-i)
      (lt_of_le_of_lt (Nat.sub_le n i) hn),
    Nat.factorization_choose hp hkn hlog,
    split_count _ hab, split_count _ hab]
  apply Nat.add_le_add hlow
  apply card_le_card
  intro a ha
  obtain ⟨ha, hd⟩ := mem_filter.mp ha
  refine mem_filter.mpr ⟨ha, high_power_carry hkn hi ?_ hd⟩
  exact lt_of_lt_of_le hcut
    (Nat.pow_le_pow_right hp.pos (mem_Ico.mp ha).1)

theorem low_power_count {p x A : ℕ} (hp : p.Prime) (hx : x ≠ 0) :
    #{a ∈ Ico 1 (A+1) | p^a ∣ x} = min A (x.factorization p) := by
  have he : {a ∈ Ico 1 (A+1) | p^a ∣ x} =
      Ico 1 (min A (x.factorization p) + 1) := by
    ext a
    simp only [mem_filter, mem_Ico, hp.pow_dvd_iff_le_factorization hx]
    omega
  rw [he, Nat.card_Ico]
  omega

/-- The truncated-covering statement in valuation form, matching the paper. -/
theorem truncated_covering_of_min {p n k i A : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hi : i < k) (hcut : k < p^(A+1))
    (hlow : min A ((n-i).factorization p) ≤
      #{a ∈ Ico 1 (A+1) | p^a ≤ k % p^a + (n-k) % p^a}) :
    (n-i).factorization p ≤ (n.choose k).factorization p := by
  apply truncated_covering hp hkn hi hcut
  rwa [low_power_count hp (by omega : n-i ≠ 0)]

/-- Primes larger than the entire window never obstruct divisibility. -/
theorem large_prime_automatic {p n k i : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hi : i < k) (hkp : k < p) :
    (n-i).factorization p ≤ (n.choose k).factorization p := by
  apply truncated_covering (A := 0) hp hkn hi (by simpa using hkp)
  simp

/-- Adding a multiple of `p^A` preserves all residues through level A. -/
theorem anchored_residue {p E x A a : ℕ} (ha : a ≤ A) (hd : p^A ∣ x) :
    (E+x) % p^a = E % p^a := by
  have hda : p^a ∣ x := dvd_trans (pow_dvd_pow p ha) hd
  simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hda]

/-- Small-prime anchor criterion. The remaining construction must establish
the explicit low-carry budget `hbudget`; this theorem does not assume the
desired full valuation inequality. -/
theorem anchored_covering {p E x k i A : ℕ} (hp : p.Prime)
    (hkn : k ≤ E+x) (hi : i < k) (hcut : k < p^(A+1)) (hd : p^A ∣ x)
    (hbudget : min A ((E+x-i).factorization p) ≤
      #{a ∈ Ico 1 (A+1) | E % p^a < k % p^a}) :
    (E+x-i).factorization p ≤ ((E+x).choose k).factorization p := by
  apply truncated_covering_of_min hp hkn hi hcut
  apply le_trans hbudget
  apply card_le_card
  intro a ha
  obtain ⟨ha, hc⟩ := mem_filter.mp ha
  refine mem_filter.mpr ⟨ha, carry_of_mod_lt hkn ?_⟩
  rwa [anchored_residue (by have := (mem_Ico.mp ha).2; omega) hd]

/-- A deeply divisible center fixes a bound for every other coordinate. -/
theorem off_center_valuation {p E x k i T : ℕ} (hp : p.Prime)
    (hkn : k ≤ E+x) (hi : i < k) (hne : i ≠ E)
    (hl : E < p^(T+1)) (hr : k-1-E < p^(T+1)) (hd : p^(T+1) ∣ x) :
    (E+x-i).factorization p ≤ T := by
  have hn : E+x-i ≠ 0 := by omega
  by_contra ht
  have hdiv : p^(T+1) ∣ E+x-i :=
    (hp.pow_dvd_iff_le_factorization hn).mpr (by omega)
  by_cases hie : i ≤ E
  · have he : E+x-i = x+(E-i) := by omega
    rw [he] at hdiv
    have hdif : p^(T+1) ∣ E-i := (Nat.dvd_add_iff_right hd).mpr hdiv
    have := Nat.le_of_dvd (by omega : 0 < E-i) hdif
    omega
  · have he : (E+x-i)+(i-E) = x := by omega
    have hdif : p^(T+1) ∣ i-E :=
      (Nat.dvd_add_iff_right hdiv).mpr (by rwa [he])
    have := Nat.le_of_dvd (by omega : 0 < i-E) hdif
    omega

/-- Extra depth at the center contributes one carry per additional level. -/
theorem anchor_carry_lower_bound {p E x k A H : ℕ} (hp : p.Prime)
    (hkn : k ≤ E+x) (hE : E < k) (hcut : k < p^(A+1))
    (hd : p^(A+H) ∣ x) :
    #{a ∈ Ico 1 (A+1) | E % p^a < k % p^a} + H ≤
      ((E+x).choose k).factorization p := by
  let b := max (Nat.log p (E+x) + 1) (A+H+1)
  have hb : A+H+1 ≤ b := le_max_right _ _
  have hlog : Nat.log p (E+x) < b :=
    lt_of_lt_of_le (by omega) (le_max_left _ _)
  rw [Nat.factorization_choose hp hkn hlog]
  let L := {a ∈ Ico 1 (A+1) | E % p^a < k % p^a}
  let U := Ico (A+1) (A+H+1)
  have hdis : Disjoint L U :=
    (Ico_disjoint_Ico_consecutive 1 (A+1) (A+H+1)).mono_left (filter_subset _ _)
  have hcU : U.card = H := by simp [U, Nat.card_Ico]
  have hcard : (L ∪ U).card = L.card + H := by
    rw [card_union_of_disjoint hdis, hcU]
  change L.card + H ≤ _
  rw [← hcard]
  apply card_le_card
  intro a ha
  rcases mem_union.mp ha with ha | ha
  · obtain ⟨ha, hc⟩ := mem_filter.mp ha
    have ha' := mem_Ico.mp ha
    apply mem_filter.mpr
    refine ⟨mem_Ico.mpr ⟨ha'.1, by omega⟩, carry_of_mod_lt hkn ?_⟩
    rwa [anchored_residue (by omega : a ≤ A+H) hd]
  · have ha' := mem_Ico.mp ha
    have hkq : k < p^a := lt_of_lt_of_le hcut
      (Nat.pow_le_pow_right hp.pos ha'.1)
    apply mem_filter.mpr
    refine ⟨mem_Ico.mpr ⟨by omega, by omega⟩, carry_of_mod_lt hkn ?_⟩
    rw [anchored_residue (by omega : a ≤ A+H) hd,
      Nat.mod_eq_of_lt (lt_trans hE hkq), Nat.mod_eq_of_lt hkq]
    exact hE

/-- The full small-prime branch, with the deficit paid by extra center depth.
Unlike `anchored_covering`, this has no unproved carry-budget premise. -/
theorem small_prime_anchor {p E x k i A T : ℕ} (hp : p.Prime)
    (hkn : k ≤ E+x) (hE : E < k) (hi : i < k) (hne : i ≠ E)
    (hcut : k < p^(A+1)) (hTA : T ≤ A)
    (hl : E < p^(T+1)) (hr : k-1-E < p^(T+1))
    (hd : p^(A + (T - #{a ∈ Ico 1 (A+1) | E % p^a < k % p^a})) ∣ x) :
    (E+x-i).factorization p ≤ ((E+x).choose k).factorization p := by
  let σ := #{a ∈ Ico 1 (A+1) | E % p^a < k % p^a}
  let H := T-σ
  change p^(A+H) ∣ x at hd
  by_cases hH : H = 0
  · have hdA : p^A ∣ x := by simpa [hH] using hd
    apply anchored_covering hp hkn hi hcut hdA
    have hTσ : T ≤ σ := by dsimp [H] at hH; omega
    change min A ((E+x-i).factorization p) ≤ σ
    by_cases hTA' : T = A
    · exact le_trans (min_le_left _ _) (by omega)
    · have hdT : p^(T+1) ∣ x := dvd_trans
        (pow_dvd_pow p (by omega : T+1 ≤ A)) hdA
      exact le_trans (min_le_right _ _)
        (le_trans (off_center_valuation hp hkn hi hne hl hr hdT) hTσ)
  · have hdT : p^(T+1) ∣ x := dvd_trans
      (pow_dvd_pow p (by omega : T+1 ≤ A+H)) hd
    have hv := off_center_valuation hp hkn hi hne hl hr hdT
    have hc := anchor_carry_lower_bound hp hkn hE hcut hd
    change σ+H ≤ _ at hc
    have hbudget : T ≤ σ+H := by dsimp [H]; omega
    exact le_trans hv (le_trans hbudget hc)

/-- The exceptional large-prime branch uses p² at the center, covering all
other factors even when the first carry is missing. -/
theorem exceptional_large_prime {p E x k i : ℕ} (hp : p.Prime)
    (hkn : k ≤ E+x) (hE : E < k) (hi : i < k) (hne : i ≠ E)
    (hcut : k < p^2) (hd : p^2 ∣ x) :
    (E+x-i).factorization p ≤ ((E+x).choose k).factorization p := by
  have hv := off_center_valuation (T := 1) hp hkn hi hne
    (lt_trans hE hcut) (by change k-1-E < p^2; omega) hd
  have hc := anchor_carry_lower_bound (A := 1) (H := 1) hp hkn hE hcut hd
  omega

theorem carry_iff_mod_lt {n k q : ℕ} (hkn : k ≤ n) (hq : 0 < q) :
    q ≤ k % q + (n-k) % q ↔ n % q < k % q := by
  refine ⟨fun hc => ?_, carry_of_mod_lt hkn⟩
  have he := Nat.add_mod_add_of_le_add_mod hc
  rw [Nat.add_sub_of_le hkn] at he
  have := Nat.mod_lt (n-k) hq
  omega

/-- Once the first nonzero digit of the center is reached, there are no more
carries. This is what makes the chosen center fail, rather than merely leaving
its divisibility undecided. -/
theorem no_late_carry {p E x k b a : ℕ} (hp : p.Prime) (hE : E < k)
    (hcut : k < p^b) (hd : p^b ∣ x) (hnd : ¬ p^(b+1) ∣ x) (ha : b < a) :
    ¬ (E+x) % p^a < k % p^a := by
  have hdba : p^b ∣ p^a := pow_dvd_pow p (by omega)
  have hkq : k < p^a := lt_of_lt_of_le hcut
    (Nat.pow_le_pow_right hp.pos (by omega))
  rw [Nat.mod_eq_of_lt hkq]
  intro hc
  have hsmall : (E+x) % p^a < p^b := lt_trans hc hcut
  have he : (E+x) % p^a = E := by
    have hm := Nat.mod_mod_of_dvd (E+x) hdba
    rw [Nat.mod_eq_of_lt hsmall, anchored_residue (le_refl b) hd,
      Nat.mod_eq_of_lt (lt_trans hE hcut)] at hm
    exact hm
  have heq : Nat.ModEq (p^a) (E+x) (E+0) := by
    show (E+x) % p^a = (E+0) % p^a
    simpa [Nat.mod_eq_of_lt (lt_trans hE hkq)] using he
  have hx0 := Nat.ModEq.add_left_cancel' E heq
  have hxa : p^a ∣ x := Nat.dvd_of_mod_eq_zero (by simpa [Nat.ModEq] using hx0)
  exact hnd (dvd_trans (pow_dvd_pow p (by omega : b+1 ≤ a)) hxa)

/-- The designated center really fails to divide the binomial coefficient
whenever a prime has a strict low-level carry deficit. -/
theorem center_fails {p E x k A : ℕ} (hp : p.Prime)
    (hkn : k ≤ E+x) (hE : E < k) (hx : x ≠ 0)
    (hcut : k < p^(A+1)) (hdA : p^(A+1) ∣ x)
    (hdef : #{a ∈ Ico 1 (A+1) | E % p^a < k % p^a} < A) :
    ¬ x ∣ (E+x).choose k := by
  let b := x.factorization p
  have hAb : A+1 ≤ b := (hp.pow_dvd_iff_le_factorization hx).mp hdA
  have hd : p^b ∣ x := (hp.pow_dvd_iff_le_factorization hx).mpr (le_refl b)
  have hnd : ¬ p^(b+1) ∣ x := by
    rw [hp.pow_dvd_iff_le_factorization hx]
    change ¬ b+1 ≤ b
    omega
  have hcutb : k < p^b := lt_of_lt_of_le hcut (Nat.pow_le_pow_right hp.pos hAb)
  let B := Nat.log p (E+x) + 1
  let L := {a ∈ Ico 1 (A+1) | E % p^a < k % p^a}
  let U := Ico (A+1) (b+1)
  have hdis : Disjoint L U :=
    (Ico_disjoint_Ico_consecutive 1 (A+1) (b+1)).mono_left (filter_subset _ _)
  have hcard : (L ∪ U).card = L.card + (b-A) := by
    rw [card_union_of_disjoint hdis]
    simp [U, Nat.card_Ico]
  have hupper : ((E+x).choose k).factorization p ≤ L.card + (b-A) := by
    rw [Nat.factorization_choose (b := B) hp hkn (by dsimp [B]; omega), ← hcard]
    apply card_le_card
    intro a ha
    obtain ⟨ha, hc⟩ := mem_filter.mp ha
    have ha1 := (mem_Ico.mp ha).1
    have hc' := (carry_iff_mod_lt hkn (pow_pos hp.pos a)).mp hc
    by_cases haA : a ≤ A
    · apply mem_union_left
      apply mem_filter.mpr
      refine ⟨mem_Ico.mpr ⟨ha1, by omega⟩, ?_⟩
      rwa [anchored_residue (by omega : a ≤ A+1) hdA] at hc'
    · apply mem_union_right
      apply mem_Ico.mpr
      refine ⟨by omega, ?_⟩
      by_contra hab
      exact no_late_carry hp hE hcutb hd hnd (by omega) hc'
  have hstrict : ((E+x).choose k).factorization p < b := by
    change L.card < A at hdef
    omega
  intro hdiv
  have hv : b ≤ ((E+x).choose k).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.choose_ne_zero hkn)).mp (dvd_trans hd hdiv)
  omega

#print axioms carry_of_mod_lt
#print axioms one_carry
#print axioms prime_power_dvd_choose
#print axioms high_power_carry
#print axioms truncated_covering
#print axioms low_power_count
#print axioms truncated_covering_of_min
#print axioms large_prime_automatic
#print axioms anchored_residue
#print axioms anchored_covering
#print axioms off_center_valuation
#print axioms anchor_carry_lower_bound
#print axioms small_prime_anchor
#print axioms exceptional_large_prime
#print axioms carry_iff_mod_lt
#print axioms no_late_carry
#print axioms center_fails
end Erdos1063

