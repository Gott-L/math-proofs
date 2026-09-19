/-
Copyright (c) 2026 Gott-L and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Formalization of Erdos and Graham, "On bases with an exact order" (1980),
Theorem 1. Gott-L set the project direction and planning; Codex implemented
the proofs. This does not claim the extremal-limit conjecture of Erdos 336.
-/
import E336Differences
import E336Padding
import E336Necessity

namespace E336

/-- The complete set-level exact-count criterion under the original bounded-basis hypothesis. -/
theorem exists_eventuallyExactly_iff {A : Set ℕ} {r : ℕ}
    (hA : EventuallyAtMost A r) :
    (∃ h : ℕ, EventuallyExactly A h) ↔ DifferenceGcdOne A := by
  constructor
  · rintro ⟨h, hh⟩
    exact differenceGcdOne_of_eventuallyExactly hh
  · intro hgcd
    exact eventuallyExactly_of_adjacentLengths hA (adjacentLengths_of_differenceGcdOne hgcd)

/-- Well-ordering gives a least exact count after existence has actually been established. -/
theorem exists_hasExactOrder_iff_exists_eventuallyExactly (A : Set ℕ) :
    (∃ h : ℕ, HasExactOrder A h) ↔ (∃ h : ℕ, EventuallyExactly A h) := by
  classical
  constructor
  · rintro ⟨h, hh, hmin⟩
    exact ⟨h, hh⟩
  · intro hex
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro j hj hjA
    exact Nat.not_le_of_lt hj (Nat.find_min' hex hjA)

/-- Erdős–Graham's full characterization, including existence of the least exact order. -/
theorem erdos_graham_set_criterion {A : Set ℕ} {r : ℕ}
    (hA : EventuallyAtMost A r) :
    (∃ h : ℕ, HasExactOrder A h) ↔ DifferenceGcdOne A := by
  rw [exists_hasExactOrder_iff_exists_eventuallyExactly]
  exact exists_eventuallyExactly_iff hA

/-- The original strictly increasing sequence / consecutive-difference formulation. -/
theorem erdos_graham_sequence_criterion {a : ℕ → ℕ} {r : ℕ}
    (ha : StrictMono a) (hA : EventuallyAtMost (Set.range a) r) :
    (∃ h : ℕ, HasExactOrder (Set.range a) h) ↔ ConsecutiveGcdOne a := by
  rw [erdos_graham_set_criterion hA]
  exact differenceGcdOne_range_iff ha

/-- A fixed eventual representation count is positive, including when zero lies in A. -/
theorem eventuallyExactly_pos {A : Set ℕ} {h : ℕ}
    (hh : EventuallyExactly A h) : 0 < h := by
  obtain ⟨N, hN⟩ := hh
  obtain ⟨xs, hlen, hxA, hsum⟩ := hN (N + 1) (by omega)
  by_contra hn
  have hz : h = 0 := by omega
  have hx : xs = [] := List.length_eq_zero_iff.mp (hlen.trans hz)
  simp only [hx, List.sum_nil] at hsum
  omega

end E336
