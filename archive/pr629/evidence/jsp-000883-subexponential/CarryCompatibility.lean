/-
Copyright 2026. Released under the Apache 2.0 license; see LICENSE.
Compatibility helpers for the PR601 formalization by 56647563 with Codex
assistance, commit 5130380a1d7f3ed00b827c666c79c89e202c3fdc.
Gott-L directed this project; Codex implemented and checked these wrappers.
They derive the newer interfaces from the pinned Mathlib 4.19 theorems.
-/
import Mathlib.Data.Nat.Choose.Factorization

namespace Nat
open Finset

theorem choose_ne_zero {n k : ℕ} (hkn : k ≤ n) : n.choose k ≠ 0 :=
  (Nat.choose_pos hkn).ne'

theorem factorization_eq_zero_of_not_prime (n : ℕ) {p : ℕ} (hp : ¬p.Prime) :
    n.factorization p = 0 := Nat.factorization_eq_zero_of_non_prime n hp

/-- The Kummer carry formula, obtained from the existing multiplicity theorem. -/
theorem factorization_choose {p n k b : ℕ} (hp : p.Prime)
    (hkn : k ≤ n) (hnb : Nat.log p n < b) :
    (n.choose k).factorization p =
      #{a ∈ Ico 1 b | p^a ≤ k % p^a + (n-k) % p^a} := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp]
  exact_mod_cast (padicValNat_eq_emultiplicity (p := p) (Nat.choose_pos hkn)) ▸
    hp.emultiplicity_choose hkn hnb

theorem factorization_eq_card_pow_dvd_of_lt {p n b : ℕ} (hp : p.Prime)
    (hn : 0 < n) (hb : n < p^b) :
    n.factorization p = #{a ∈ Ico 1 b | p^a ∣ n} := by
  have hv : n.factorization p < b :=
    (Nat.pow_lt_pow_iff_right hp.one_lt).mp ((Nat.ordProj_le p hn.ne').trans_lt hb)
  have he : {a ∈ Ico 1 b | p^a ∣ n} = Icc 1 (n.factorization p) := by
    ext a
    simp only [mem_filter, mem_Ico, mem_Icc, hp.pow_dvd_iff_le_factorization hn.ne']
    omega
  rw [he, Nat.card_Icc]
  omega

end Nat
