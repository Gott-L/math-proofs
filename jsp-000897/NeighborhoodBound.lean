import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
An elementary edge count outside an induced subgraph. Every edge not wholly in
the selected vertex set is incident to a vertex of its complement. Counting
incidences may count some edges twice, which is harmless for the upper bound.
No extremal graph theorem is used.
-/

open scoped BigOperators
open Finset

namespace GottL897

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem edge_card_le_internal_add_complement_degrees (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Finset V) :
    G.edgeFinset.card ≤ (G.edgeFinset ∩ S.sym2).card + ∑ w ∈ Sᶜ, G.degree w := by
  classical
  have hcover : G.edgeFinset ⊆
      (G.edgeFinset ∩ S.sym2) ∪ Sᶜ.biUnion (fun w => G.incidenceFinset w) := by
    intro e he
    by_cases hi : e ∈ S.sym2
    · exact mem_union_left _ (mem_inter.mpr ⟨he, hi⟩)
    · apply mem_union_right
      induction e using Sym2.inductionOn with
      | _ a b =>
        simp only [mk_mem_sym2_iff, not_and_or] at hi
        rcases hi with ha | hb
        · apply mem_biUnion.mpr
          refine ⟨a, mem_compl.mpr ha, ?_⟩
          rw [G.incidenceFinset_eq_filter]
          exact mem_filter.mpr ⟨he, by simp⟩
        · apply mem_biUnion.mpr
          refine ⟨b, mem_compl.mpr hb, ?_⟩
          rw [G.incidenceFinset_eq_filter]
          exact mem_filter.mpr ⟨he, by simp⟩
  calc
    G.edgeFinset.card ≤
        ((G.edgeFinset ∩ S.sym2) ∪ Sᶜ.biUnion (fun w => G.incidenceFinset w)).card :=
      card_le_card hcover
    _ ≤ (G.edgeFinset ∩ S.sym2).card + (Sᶜ.biUnion (fun w => G.incidenceFinset w)).card :=
      card_union_le _ _
    _ ≤ (G.edgeFinset ∩ S.sym2).card + ∑ w ∈ Sᶜ, (G.incidenceFinset w).card :=
      Nat.add_le_add_left (card_biUnion_le) _
    _ = (G.edgeFinset ∩ S.sym2).card + ∑ w ∈ Sᶜ, G.degree w := by simp

theorem edge_card_le_induce_add_complement_degrees (G : SimpleGraph V)
    [DecidableRel G.Adj] (S : Set V) [DecidablePred (· ∈ S)] :
    G.edgeFinset.card ≤ (G.induce S).edgeFinset.card +
      ∑ w ∈ S.toFinsetᶜ, G.degree w := by
  classical
  have hcard : (G.edgeFinset ∩ S.toFinset.sym2).card =
      (G.induce S).edgeFinset.card := by
    rw [← G.map_edgeFinset_induce, card_map]
  simpa only [hcard] using edge_card_le_internal_add_complement_degrees G S.toFinset

/-- The neighborhood of a maximum-degree vertex supplies the internal edge term. -/
theorem neighborhood_edge_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (v : Fin n)
    (hdeg : ∀ w, G.degree w ≤ G.degree v) :
    G.edgeFinset.card ≤ (G.induce (G.neighborSet v)).edgeFinset.card +
      (n - G.degree v) * G.degree v := by
  classical
  have hsum : ∑ w ∈ (G.neighborSet v).toFinsetᶜ, G.degree w ≤
      (n - G.degree v) * G.degree v := by
    calc
      ∑ w ∈ (G.neighborSet v).toFinsetᶜ, G.degree w ≤
          ∑ _w ∈ (G.neighborSet v).toFinsetᶜ, G.degree v :=
        sum_le_sum fun w _ => hdeg w
      _ = (n - G.degree v) * G.degree v := by
        simp [card_compl, SimpleGraph.degree, SimpleGraph.neighborFinset]
  exact (edge_card_le_induce_add_complement_degrees G (G.neighborSet v)).trans
    (Nat.add_le_add_left hsum _)

end GottL897
