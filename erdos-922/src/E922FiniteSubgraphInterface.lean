import E922FiniteInterface

/-!
Finite-subgraph formulation on an arbitrary ambient vertex type. The
finite-only source's two elementary transport arguments are adapted here
with the finiteness instance supplied locally for each tested subgraph.
Inherited source: plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
Erdos922.lean, original lines 58--108. Original mathematics and formal credits
remain with their authors. Codex supplied this integration under Gott-L's
direction. Private local work; no redistribution license or priority claim.
-/

namespace Erdos922Adapter

universe u

/-- Every finite subgraph, including graphs with deleted edges, has an
independent subset of the required cardinality. The ambient graph may be
infinite, uncountable, or have vertices of infinite degree. -/
def LargeIndependentFiniteSubgraphs {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ H : G.Subgraph, H.verts.Finite → ∃ I : Finset H.verts,
    H.coe.IsIndepSet I ∧ H.verts.ncard ≤ 2 * I.card + k

theorem localCondition_iff_finiteSubgraphs {V : Type u}
    (G : SimpleGraph V) (k : ℕ) :
    LargeIndependentFinsets G k ↔ LargeIndependentFiniteSubgraphs G k := by
  classical
  rw [localCondition_iff_publicFinsets]
  constructor
  · intro h H hfinite
    letI : Fintype H.verts := hfinite.fintype
    let S : Finset V := H.verts.toFinset
    obtain ⟨I, hIS, hI, hcard⟩ := h S
    let J : Finset H.verts := I.subtype (fun v ↦ v ∈ H.verts)
    refine ⟨J, ?_, ?_⟩
    · rw [SimpleGraph.isIndepSet_iff]
      intro a ha b hb hab
      have haI : a.1 ∈ I := by
        change a ∈ J at ha
        simpa only [J, Finset.mem_subtype] using ha
      have hbI : b.1 ∈ I := by
        change b ∈ J at hb
        simpa only [J, Finset.mem_subtype] using hb
      exact fun hAdj ↦ hI haI hbI (Subtype.coe_ne_coe.mpr hab)
        (H.coe_adj_sub a b hAdj)
    · have hIfilter : I.filter (fun v ↦ v ∈ H.verts) = I := by
        exact Finset.filter_eq_self.mpr fun v hv ↦ by
          have : v ∈ S := hIS hv
          simpa only [S, Set.mem_toFinset] using this
      have hJcard : J.card = I.card := by
        simp only [J, Finset.card_subtype, hIfilter]
      rw [Set.ncard_eq_toFinset_card']
      simpa only [S, hJcard] using hcard
  · intro h S
    let H : G.Subgraph := (⊤ : G.Subgraph).induce (↑S : Set V)
    have hfinite : H.verts.Finite := S.finite_toSet
    obtain ⟨J, hJ, hcard⟩ := h H hfinite
    let I : Finset V := J.map ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨I, ?_, ?_, ?_⟩
    · intro v hv
      simp only [I, Finset.mem_map, Function.Embedding.coeFn_mk] at hv
      obtain ⟨w, hw, rfl⟩ := hv
      exact w.property
    · have himage : G.IsIndepSet (Subtype.val '' (↑J : Set H.verts)) := by
        exact (SimpleGraph.isIndepSet_induce (G := G)).mp hJ
      simpa only [I, Finset.coe_map, Function.Embedding.coeFn_mk] using himage
    · simpa only [H, SimpleGraph.Subgraph.induce_verts, Set.ncard_coe_Finset,
        I, Finset.card_map] using hcard

end Erdos922Adapter
