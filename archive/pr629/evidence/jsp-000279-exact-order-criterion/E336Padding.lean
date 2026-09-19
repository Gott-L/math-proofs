/-
Copyright (c) 2026 Gott-L and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Known mathematical argument: Erdős–Graham (1980), Theorem 1.
Gott-L directed and coordinated this project; Codex implemented this module.
-/
import E336Defs

namespace E336

theorem representsExactly_zero (A : Set ℕ) : RepresentsExactly A 0 0 :=
  ⟨[], rfl, by simp, rfl⟩

/-- Concatenation adds both the number of terms and the represented value. -/
theorem representsExactly_add {A : Set ℕ} {h k n m : ℕ}
    (hn : RepresentsExactly A h n) (hm : RepresentsExactly A k m) :
    RepresentsExactly A (h + k) (n + m) := by
  obtain ⟨xs, hxs, hxA, hxsum⟩ := hn
  obtain ⟨ys, hys, hyA, hysum⟩ := hm
  refine ⟨xs ++ ys, by simp [hxs, hys], ?_, by simp [hxsum, hysum]⟩
  intro z hz
  rcases List.mem_append.mp hz with hz | hz
  · exact hxA z hz
  · exact hyA z hz

/-- `r` copies of the same value admit every length from `r*L` to `r*(L+1)`. -/
theorem representsExactly_adjacent_padding {A : Set ℕ} {L M : ℕ}
    (hshort : RepresentsExactly A L M) (hlong : RepresentsExactly A (L + 1) M)
    (r : ℕ) :
    ∀ j : ℕ, j ≤ r → RepresentsExactly A (r * L + j) (r * M) := by
  induction r with
  | zero =>
      intro j hj
      have hj0 : j = 0 := by omega
      simpa [hj0] using representsExactly_zero A
  | succ r ih =>
      intro j hj
      by_cases hjr : j ≤ r
      · have h := representsExactly_add (ih j hjr) hshort
        have hlen : r * L + j + L = (r + 1) * L + j := by
          rw [Nat.add_mul, Nat.one_mul]
          omega
        simpa only [hlen, Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] using h
      · have hjlast : j = r + 1 := by omega
        subst j
        have h := representsExactly_add (ih r le_rfl) hlong
        have hlen : r * L + r + (L + 1) = (r + 1) * L + (r + 1) := by
          rw [Nat.add_mul, Nat.one_mul]
          omega
        simpa only [hlen, Nat.succ_eq_add_one, Nat.add_mul, Nat.one_mul] using h

/-- The finite adjacent-length certificate gives a fixed eventual length.
The proof uses the explicit threshold `N + r*M` when `N` is a weak-basis threshold. -/
theorem eventuallyExactly_of_adjacent_representations {A : Set ℕ} {r L M : ℕ}
    (hA : EventuallyAtMost A r)
    (hshort : RepresentsExactly A L M) (hlong : RepresentsExactly A (L + 1) M) :
    EventuallyExactly A (r * (L + 1)) := by
  obtain ⟨N, hN⟩ := hA
  refine ⟨N + r * M, ?_⟩
  intro n hn
  obtain ⟨j, hjr, hj⟩ := hN (n - r * M) (by omega)
  have hpad := representsExactly_adjacent_padding hshort hlong r (r - j) (by omega)
  have h := representsExactly_add hj hpad
  have hlen : j + (r * L + (r - j)) = r * (L + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hsum : n - r * M + r * M = n := by omega
  simpa only [hlen, hsum] using h

/-- The modular-arithmetic module will provide `AdjacentLengths A` from gcd one. -/
theorem eventuallyExactly_of_adjacentLengths {A : Set ℕ} {r : ℕ}
    (hA : EventuallyAtMost A r) (hadj : AdjacentLengths A) :
    ∃ h : ℕ, EventuallyExactly A h := by
  obtain ⟨L, M, hshort, hlong⟩ := hadj
  exact ⟨r * (L + 1), eventuallyExactly_of_adjacent_representations hA hshort hlong⟩

end E336
