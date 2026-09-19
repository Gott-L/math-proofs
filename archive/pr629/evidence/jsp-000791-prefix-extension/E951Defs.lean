/-
Copyright (c) 2026. Released under the Apache License, Version 2.0.
Project initiation, conception, objectives, planning and research direction: Gott-L.
Research, formal proof implementation and internal checks: Codex assistance.
Known extension argument: Barreto--Price and Patrick White with Claude;
this is a new implementation, not a mathematical discovery claim.
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace E951

def monomial {n : ℕ} (a : Fin n → ℝ) (u : Fin n → ℕ) : ℝ :=
  ∏ i, a i ^ u i

def Separated {n : ℕ} (a : Fin n → ℝ) : Prop :=
  ∀ u v : Fin n → ℕ, u ≠ v → 1 ≤ |monomial a u - monomial a v|

def Avoids {n : ℕ} (a : Fin n → ℝ) (x : ℝ) : Prop :=
  ∀ u v : Fin n → ℕ, ∀ k : ℕ, 1 ≤ |monomial a u * x ^ (k + 1) - monomial a v|

noncomputable def weight {n : ℕ} (a : Fin n → ℝ) (u : Fin n → ℕ) : ℝ :=
  (Real.sqrt (monomial a u))⁻¹

def sequenceMonomial (a : ℕ → ℝ) (u : ℕ →₀ ℕ) : ℝ :=
  u.prod (fun i k => a i ^ k)

def SequenceSeparated (a : ℕ → ℝ) : Prop :=
  ∀ u v : ℕ →₀ ℕ, u ≠ v → 1 ≤ |sequenceMonomial a u - sequenceMonomial a v|

end E951
