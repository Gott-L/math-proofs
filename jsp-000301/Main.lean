import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Group.Even
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
An independently written proof of the complete yes/no question JSP-000301.
The classical pair 12167, 12168 is not a new mathematical discovery. Earlier
Lean implementations of this question were known before this implementation;
no problem-specific Lean code is copied or imported here. The mathematics is
credited to the literature on powerful numbers cited in the official catalogue
(Golomb, Walker, and Guy); no first-counterexample attribution is asserted.

Gott-L directed the project; Codex wrote this implementation. This file resolves
the catalogue's consecutive-powerful-nonsquares question only, and does not
assert a solution of the separate counting or infinitude questions of E365.
-/

namespace GottL301

/-- A positive integer is powerful if each of its prime divisors divides it
to at least the second power. Positivity is part of the definition. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

/-- The ordered pair consists of consecutive natural numbers. -/
def Consecutive (a b : ℕ) : Prop := b = a + 1

/-- A square of a positive integer is powerful. -/
theorem powerful_square {a : ℕ} (ha : 0 < a) : Powerful (a ^ 2) := by
  refine ⟨pow_pos ha _, ?_⟩
  intro p hp hpa
  obtain ⟨d, hd⟩ := hp.dvd_of_dvd_pow hpa
  refine ⟨d ^ 2, ?_⟩
  rw [hd]
  ring

/-- A cube of a positive integer is powerful. -/
theorem powerful_cube {a : ℕ} (ha : 0 < a) : Powerful (a ^ 3) := by
  refine ⟨pow_pos ha _, ?_⟩
  intro p hp hpa
  obtain ⟨d, hd⟩ := hp.dvd_of_dvd_pow hpa
  refine ⟨p * d ^ 3, ?_⟩
  rw [hd]
  ring

/-- Products preserve powerfulness; no coprimality assumption is needed. -/
theorem powerful_mul {a b : ℕ} (ha : Powerful a) (hb : Powerful b) :
    Powerful (a * b) := by
  refine ⟨Nat.mul_pos ha.1 hb.1, ?_⟩
  intro p hp hab
  rcases hp.dvd_mul.mp hab with hpa | hpb
  · exact dvd_mul_of_dvd_left (ha.2 p hp hpa) b
  · exact dvd_mul_of_dvd_right (hb.2 p hp hpb) a

/-- There is no natural-number square strictly between consecutive squares. -/
theorem not_isSquare_between {n a : ℕ}
    (hlo : a ^ 2 < n) (hhi : n < (a + 1) ^ 2) : ¬ IsSquare n := by
  rintro ⟨r, hr⟩
  rcases le_or_gt r a with hle | hgt
  · have hs := Nat.mul_self_le_mul_self hle
    nlinarith
  · have hs := Nat.mul_self_le_mul_self (Nat.succ_le_of_lt hgt)
    nlinarith

theorem powerful_12167 : Powerful 12167 := by
  have h := powerful_cube (a := 23) (by norm_num)
  norm_num at h ⊢
  exact h

theorem powerful_12168 : Powerful 12168 := by
  have h := powerful_mul
    (powerful_cube (a := 2) (by norm_num))
    (powerful_square (a := 39) (by norm_num))
  norm_num at h ⊢
  exact h

theorem not_isSquare_12167 : ¬ IsSquare (12167 : ℕ) :=
  not_isSquare_between (a := 110) (by norm_num) (by norm_num)

theorem not_isSquare_12168 : ¬ IsSquare (12168 : ℕ) :=
  not_isSquare_between (a := 110) (by norm_num) (by norm_num)

/-- A complete counterexample to the catalogue's universal yes/no assertion. -/
theorem exists_consecutive_powerful_nonsquares :
    ∃ n : ℕ, 0 < n ∧ Powerful n ∧ Powerful (n + 1) ∧
      ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := by
  refine ⟨12167, by norm_num, powerful_12167, ?_, not_isSquare_12167, ?_⟩
  · exact powerful_12168
  · exact not_isSquare_12168

/-- An explicit two-variable form retaining positivity and consecutiveness. -/
theorem exists_positive_consecutive_pair :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ Consecutive a b ∧
      Powerful a ∧ Powerful b ∧ ¬ IsSquare a ∧ ¬ IsSquare b := by
  obtain ⟨n, hn, hp, hnext, hns, hnextns⟩ :=
    exists_consecutive_powerful_nonsquares
  exact ⟨n, n + 1, hn, Nat.zero_lt_succ n, rfl, hp, hnext, hns, hnextns⟩

/-- The literal catalogue assertion, expressed for all ordered pairs. -/
def CatalogClaim : Prop :=
  ∀ a b : ℕ, Powerful a → Powerful b → Consecutive a b →
    IsSquare a ∨ IsSquare b

/-- JSP-000301 has a negative answer. -/
theorem not_catalog_claim : ¬ CatalogClaim := by
  intro h
  obtain ⟨n, _, hp, hnext, hns, hnextns⟩ :=
    exists_consecutive_powerful_nonsquares
  exact (h n (n + 1) hp hnext rfl).elim hns hnextns

/-- The same negative answer with the positive integer quantified directly. -/
theorem not_all_consecutive_powerful_have_square :
    ¬ (∀ n : ℕ, 0 < n → Powerful n → Powerful (n + 1) →
      IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  obtain ⟨n, hn, hp, hnext, hns, hnextns⟩ :=
    exists_consecutive_powerful_nonsquares
  exact (h n hn hp hnext).elim hns hnextns

end GottL301
