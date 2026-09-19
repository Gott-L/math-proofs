/-
Copyright (c) 2026 Gott-L and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Mathematical theorem: P. Erdős and R. L. Graham, "On bases with an exact order",
Acta Arithmetica 37 (1980), Theorem 1, pp. 202–203.
Gott-L directed and coordinated this project; Codex implemented this module.
This is a formalization of a known theorem, not a claim of new mathematics.
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.Dist

/-! Elementary definitions for the exact-order characterization. Lists allow
repeated summands, and zero belongs to the ambient natural numbers. -/

namespace E336

/-- A representation with exactly `h` terms, allowing repetitions. -/
def RepresentsExactly (A : Set ℕ) (h n : ℕ) : Prop :=
  ∃ xs : List ℕ, xs.length = h ∧ (∀ x ∈ xs, x ∈ A) ∧ xs.sum = n

/-- One fixed term count represents every sufficiently large natural number. -/
def EventuallyExactly (A : Set ℕ) (h : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → RepresentsExactly A h n

/-- A uniform upper bound on the number of terms suffices eventually. -/
def EventuallyAtMost (A : Set ℕ) (r : ℕ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∃ h : ℕ, h ≤ r ∧ RepresentsExactly A h n

/-- The least fixed term count that suffices eventually. -/
def HasExactOrder (A : Set ℕ) (h : ℕ) : Prop :=
  EventuallyExactly A h ∧ ∀ j : ℕ, j < h → ¬ EventuallyExactly A j

/-- The universal divisibility characterization of gcd one for all differences. -/
def DifferenceGcdOne (A : Set ℕ) : Prop :=
  ∀ d : ℕ, (∀ x ∈ A, ∀ y ∈ A, d ∣ Nat.dist x y) → d = 1

/-- The original consecutive-difference condition, for an increasing enumeration. -/
def ConsecutiveGcdOne (a : ℕ → ℕ) : Prop :=
  ∀ d : ℕ, (∀ i : ℕ, d ∣ a (i + 1) - a i) → d = 1

/-- A finite certificate: one value admits two adjacent representation lengths. -/
def AdjacentLengths (A : Set ℕ) : Prop :=
  ∃ L M : ℕ, RepresentsExactly A L M ∧ RepresentsExactly A (L + 1) M

end E336
