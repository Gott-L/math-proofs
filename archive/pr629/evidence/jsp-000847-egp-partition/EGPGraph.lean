/-
Copyright (c) 2026. Released under the Apache License, Version 2.0.
Project initiation, conception, objectives, planning and research direction: Gott-L.
Research, formal proof implementation and internal checks: Codex assistance.
Mathematical theorem: Erdos, Goodman and Posa (1966), Theorem 4.
-/
import EGPSubmission
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace EGP

/-- Every finite simple graph admits an exact partition into edges and triangles. -/
theorem simple_graph_partition {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ P : Finset (Finset V), P.card ≤ Fintype.card V ^ 2 / 4 ∧
      (∀ p ∈ P, (p.card = 2 ∨ p.card = 3) ∧
        ∀ a ∈ p, ∀ b ∈ p, a ≠ b → G.Adj a b) ∧
      (∀ a b, G.Adj a b → ∃! p, p ∈ P ∧ a ∈ p ∧ b ∈ p) := by
  classical
  obtain ⟨P, hP, hcard⟩ := erdos_goodman_posa Finset.univ G.Adj G.symm G.loopless
  refine ⟨P, by simpa using hcard, ?_, ?_⟩
  · intro p hp
    exact ⟨(hP.1 p hp).2.1, (hP.1 p hp).2.2⟩
  · intro a b hab
    exact hP.2 a (Finset.mem_univ a) b (Finset.mem_univ b) hab

end EGP
