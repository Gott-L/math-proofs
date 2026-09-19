/-
Copyright (c) 2026. Released under the Apache License, Version 2.0.
Project initiation, conception, objectives, planning and research direction: Gott-L.
Research, formal proof implementation and internal checks: Codex assistance.
Mathematical theorem: Erdos, Goodman and Posa (1966), Theorem 4.
-/
import EGPInduction
import EGPAssembly
import Mathlib.Data.Fintype.Card

namespace EGP

variable {V : Type*}

/-- The complete classical Erdős–Goodman–Pósa edge/triangle partition bound.
No existence or matching hypothesis remains in this endpoint. -/
theorem erdos_goodman_posa (S : Finset V) (R : V → V → Prop)
    (hs : Symmetric R) (hi : Irreflexive R) :
    ∃ P, PartitionOn S R P ∧ P.card ≤ S.card ^ 2 / 4 := by
  classical
  exact partition_bound_of_extension extend_partition S R hs hi

/-- A literal finite-vertex formulation, exposing every partition condition. -/
theorem finite_relation_partition (n : ℕ) (R : Fin n → Fin n → Prop)
    (hs : Symmetric R) (hi : Irreflexive R) :
    ∃ P : Finset (Finset (Fin n)), P.card ≤ n ^ 2 / 4 ∧
      (∀ p ∈ P, (p.card = 2 ∨ p.card = 3) ∧
        ∀ a ∈ p, ∀ b ∈ p, a ≠ b → R a b) ∧
      (∀ a b, R a b → ∃! p, p ∈ P ∧ a ∈ p ∧ b ∈ p) := by
  obtain ⟨P, hP, hcard⟩ := erdos_goodman_posa Finset.univ R hs hi
  refine ⟨P, by simpa using hcard, ?_, ?_⟩
  · intro p hp
    exact ⟨(hP.1 p hp).2.1, (hP.1 p hp).2.2⟩
  · intro a b hab
    exact hP.2 a (Finset.mem_univ a) b (Finset.mem_univ b) hab

end EGP
