/-
Copyright (c) 2026 Gott-L and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Gott-L directed and coordinated this project; Codex implemented this module.
The mathematical criterion is due to Erdős and Graham (1980).
-/
import E336Defs
import Mathlib.Data.Nat.ModEq

namespace E336

/-- Congruence is equivalent to divisibility of the unsigned difference. -/
theorem modEq_iff_dvd_dist (d x y : ℕ) : Nat.ModEq d x y ↔ d ∣ Nat.dist x y := by
  rcases le_total x y with hxy | hyx
  · rw [Nat.dist_eq_sub_of_le hxy]
    exact Nat.modEq_iff_dvd' hxy
  · rw [Nat.dist_eq_sub_of_le_right hyx]
    constructor
    · intro h
      exact (Nat.modEq_iff_dvd' hyx).mp h.symm
    · intro h
      exact ((Nat.modEq_iff_dvd' hyx).mpr h).symm

/-- Equal-length lists with entries in one residue class have congruent sums. -/
theorem list_sums_modEq {A : Set ℕ} {d : ℕ}
    (hd : ∀ x ∈ A, ∀ y ∈ A, d ∣ Nat.dist x y)
    (xs ys : List ℕ) (hlen : xs.length = ys.length)
    (hxA : ∀ x ∈ xs, x ∈ A) (hyA : ∀ y ∈ ys, y ∈ A) :
    Nat.ModEq d xs.sum ys.sum := by
  induction xs generalizing ys with
  | nil =>
      have hy : ys = [] := List.length_eq_zero_iff.mp hlen.symm
      subst ys
      exact Nat.ModEq.refl _
  | cons x xs ih =>
      cases ys with
      | nil => simp at hlen
      | cons y ys =>
          have hxy : Nat.ModEq d x y :=
            (modEq_iff_dvd_dist d x y).mpr
              (hd x (hxA x (by simp)) y (hyA y (by simp)))
          have htail : Nat.ModEq d xs.sum ys.sum :=
            ih ys (by simpa using hlen)
              (fun z hz => hxA z (by simp [hz]))
              (fun z hz => hyA z (by simp [hz]))
          simpa using hxy.add htail

/-- A fixed exact order precludes any nontrivial common divisor of differences. -/
theorem differenceGcdOne_of_eventuallyExactly {A : Set ℕ} {h : ℕ}
    (hA : EventuallyExactly A h) : DifferenceGcdOne A := by
  obtain ⟨N, hN⟩ := hA
  intro d hd
  obtain ⟨xs, hxlen, hxA, hxsum⟩ := hN N le_rfl
  obtain ⟨ys, hylen, hyA, hysum⟩ := hN (N + 1) (by omega)
  have hmod : Nat.ModEq d N (N + 1) := by
    simpa only [hxsum, hysum] using
      list_sums_modEq hd xs ys (hxlen.trans hylen.symm) hxA hyA
  have hdiv : d ∣ 1 := by
    simpa using (Nat.modEq_iff_dvd' (Nat.le_succ N)).mp hmod
  exact Nat.dvd_one.mp hdiv

/-- All pairwise differences and all consecutive differences have the same
common divisors in a strictly increasing natural-number sequence. -/
theorem pairwise_dvd_iff_consecutive_dvd {a : ℕ → ℕ}
    (ha : StrictMono a) (d : ℕ) :
    (∀ x ∈ Set.range a, ∀ y ∈ Set.range a, d ∣ Nat.dist x y) ↔
      ∀ i : ℕ, d ∣ a (i + 1) - a i := by
  constructor
  · intro hd i
    have h := hd (a i) ⟨i, rfl⟩ (a (i + 1)) ⟨i + 1, rfl⟩
    simpa only [Nat.dist_eq_sub_of_le (ha.monotone (Nat.le_succ i))] using h
  · intro hd
    have hbase : ∀ i : ℕ, Nat.ModEq d (a 0) (a i) := by
      intro i
      induction i with
      | zero => exact Nat.ModEq.refl _
      | succ i ih =>
          exact ih.trans ((Nat.modEq_iff_dvd'
            (ha.monotone (Nat.le_succ i))).mpr (hd i))
    rintro x ⟨i, rfl⟩ y ⟨j, rfl⟩
    exact (modEq_iff_dvd_dist d (a i) (a j)).mp ((hbase i).symm.trans (hbase j))

/-- This bridges the set statement to the consecutive-difference wording
of Erdős–Graham's theorem, with no extra divisibility assumption. -/
theorem differenceGcdOne_range_iff {a : ℕ → ℕ} (ha : StrictMono a) :
    DifferenceGcdOne (Set.range a) ↔ ConsecutiveGcdOne a := by
  constructor
  · intro h d hd
    exact h d ((pairwise_dvd_iff_consecutive_dvd ha d).mpr hd)
  · intro h d hd
    exact h d ((pairwise_dvd_iff_consecutive_dvd ha d).mp hd)

end E336
