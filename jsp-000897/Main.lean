import JoinBound
import NeighborhoodBound
import DegreeBound

/-!
Complete dense-neighbourhood theorem for JSP-000897 / Erdős 1079.
This is known mathematics (Bollobás--Thomason, Erdős--Sós, and the strict
strengthening associated with Bondy), with existing full formalizations.
Gott-L initiated and planned the project; Codex reconstructed and implemented
this proof using the finite extremal definition without Turán's theorem.
No problem-specific source from the prior implementations is imported here.
-/

namespace GottL897

open SimpleGraph

/-- The edge surplus over the global clique threshold persists in the open
neighbourhood of every maximum-degree vertex. -/
theorem neighborhood_surplus {n r : ℕ} (hr : 3 ≤ r)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n)
    (hv : G.degree v = G.maxDegree) :
    SimpleGraph.extremalNumber (G.degree v) (⊤ : SimpleGraph (Fin (r - 1))) +
        G.edgeFinset.card ≤
      (G.induce (G.neighborSet v)).edgeFinset.card +
        SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) := by
  classical
  have hd : G.degree v ≤ n := by
    simpa using (G.degree_lt_card_verts v).le
  have hdeg : ∀ w, G.degree w ≤ G.degree v := by
    intro w
    rw [hv]
    exact G.degree_le_maxDegree w
  have hcount := neighborhood_edge_bound G v hdeg
  have hjoin := clique_extremal_join_le hr hd
  rw [Nat.mul_comm (G.degree v) (n - G.degree v)] at hjoin
  omega

/-- Complete non-strict form of the catalogue question. In particular the
degree is uniformly at least half the order, for all n ≥ 2 and r ≥ 4. -/
theorem dense_neighborhood {n r : ℕ} (hr : 4 ≤ r) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) ≤
      G.edgeFinset.card) :
    ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      SimpleGraph.extremalNumber (G.degree v) (⊤ : SimpleGraph (Fin (r - 1))) ≤
        (G.induce (G.neighborSet v)).edgeFinset.card := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hsurplus := neighborhood_surplus (by omega : 3 ≤ r) G v hv.symm
  have hlinear := card_le_twice_maxDegree_of_extremal_threshold hr hn G hG
  refine ⟨v, hv.symm, ?_, ?_⟩
  · simpa [hv] using hlinear
  · omega

/-- The strict edge threshold gives a strict neighbourhood threshold for the
same maximum-degree choice, while preserving the complete linear bound. -/
theorem dense_neighborhood_strict {n r : ℕ} (hr : 4 ≤ r) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) <
      G.edgeFinset.card) :
    ∃ v : Fin n, G.degree v = G.maxDegree ∧ n ≤ 2 * G.degree v ∧
      SimpleGraph.extremalNumber (G.degree v) (⊤ : SimpleGraph (Fin (r - 1))) <
        (G.induce (G.neighborSet v)).edgeFinset.card := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hsurplus := neighborhood_surplus (by omega : 3 ≤ r) G v hv.symm
  have hlinear := card_le_twice_maxDegree_of_extremal_threshold hr hn G hG.le
  refine ⟨v, hv.symm, ?_, ?_⟩
  · simpa [hv] using hlinear
  · omega

end GottL897
