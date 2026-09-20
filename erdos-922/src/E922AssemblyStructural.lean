/-
Inherited finite Folkman proof from plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
Original informal mathematics: Jon Folkman; formal source: Codex / GPT-5.6 Sol.
Local Lean 4.19 compatibility and integration: Codex under Gott-L direction.
Private local work; upstream redistribution license unverified. No priority claim.
-/
import E922AssemblyNumerics
import E922AttachmentsCore
import E922RecolorFinal

namespace Erdos922Assembly
open SimpleGraph
universe u

/-- The abstract even-hole exclusion specializes to the local induced-C4
predicate used by the maximum-clique recoloring. -/
theorem noInducedFourCycle_of_orderMinimal
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G) :
    Erdos922Recolor.NoInducedFourCycle G := by
  classical
  intro a b c d hab hac had hbc hbd hcd hAB hBC hCD hDA hAC hBD
  apply Erdos922.EvenHole.no_configuration_of_orderMinimalCounterexample G hmin
  exact ⟨{a, c}, {b, d}, 2,
    evenHoleConfiguration_of_inducedFourCycle hab hac had hbc hbd hcd
      hAB hBC hCD hDA hAC hBD⟩

/-- Common-neighbor cliquehood is exactly the local no-induced-diamond
predicate used by the recoloring layer. -/
theorem noInducedDiamond_of_orderMinimal
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G) :
    Erdos922Recolor.NoInducedDiamond G := by
  classical
  letI : DecidableRel G.Adj := Classical.decRel G.Adj
  intro a b c d hab hac had hbc hbd hcd hAB hAC hBC hAD hBD hCD
  have hclique := Erdos922Diamond.commonNeighbors_isClique_of_orderMinimalCounterexample
    hmin a b hAB
  exact hCD (hclique ⟨hAC, hBC⟩ ⟨hAD, hBD⟩ hcd)

/-- The maximum-clique recoloring rules out a triangle in an order-minimal
counterexample once diamonds and induced four-cycles have been excluded. -/
theorem triangle_free_of_orderMinimal
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (hdiamond : Erdos922Recolor.NoInducedDiamond G)
    (hfour : Erdos922Recolor.NoInducedFourCycle G) :
    G.CliqueFree 3 := by
  classical
  intro T hT
  obtain ⟨K, hK⟩ := G.maximumClique_exists
  have hKcard : 3 ≤ K.card := by
    have hle := hK.maximum T hT.isClique
    simpa [hT.card_eq] using hle
  have hKne : K.Nonempty := Finset.card_pos.mp (by omega)
  have hKalpha : Erdos922FullB.alphaOn G K = 1 :=
    alphaOn_eq_one_of_nonempty_clique hK.isClique hKne
  have hKpot : Erdos922FullB.potential G K = (K.card : ℤ) - 2 := by
    simp [Erdos922FullB.potential, hKalpha]
  have hKf : (K.card : ℤ) - 2 ≤
      Erdos922FullB.fOn G (Finset.univ : Finset V) := by
    rw [← hKpot]
    exact Erdos922FullB.potential_le_fOn G (Finset.subset_univ K)
  have hgap := Erdos922FullB.counterexample_gap_int G hmin.counterexample
  have hKltchi : K.card < Erdos922FullB.chiNat G := by omega
  have hKnotuniv : K ≠ (Finset.univ : Finset V) := by
    intro hKuniv
    have hc : G.Colorable K.card := by
      simpa [hKuniv] using G.colorable_of_fintype
    have hchi : Erdos922FullB.chiNat G ≤ K.card :=
      (Erdos922FullB.colorable_iff_chiNat_le G K.card).mp hc
    omega
  let q : ℕ := Erdos922FullB.chiNat G - 2
  have hq : q + 1 = Erdos922FullB.chiNat G - 1 := by
    dsimp only [q]
    omega
  have hKfit : K.card ≤ q + 1 := by
    rw [hq]
    omega
  have hsplit := hmin.critical_split K hKne hKnotuniv
  have hKchi : K.card ≤
      Erdos922FullB.chiNat (G.induce (K : Set V)) := by
    let KU : Finset (K : Set V) := Finset.univ
    have hKU : (G.induce (K : Set V)).IsClique (KU : Set (K : Set V)) := by
      intro a _ha b _hb hab
      exact hK.isClique a.2 b.2 (fun e ↦ hab (Subtype.ext e))
    have hc := hKU.card_le_of_colorable
      (Erdos922FullB.colorable_chiNat (G.induce (K : Set V)))
    simpa [KU] using hc
  have houtchi : Erdos922FullB.chiNat
      (G.induce ((K : Set V)ᶜ)) ≤ q := by
    rw [show ((↑(Kᶜ) : Set V)) = ((K : Set V)ᶜ) by ext v; simp] at hsplit
    dsimp only [q]
    omega
  obtain ⟨outsideColor⟩ : (G.induce ((K : Set V)ᶜ)).Colorable q :=
    (Erdos922FullB.colorable_iff_chiNat_le _ q).mpr houtchi
  have hcolor : G.Colorable (q + 1) :=
    Erdos922Recolor.maximumClique_final_recoloring_of_card_le G q K
      hK.isClique hKfit outsideColor
      (Erdos922Recolor.maximalClique_attachment_unique G
        (hK.isMaximalClique K) hdiamond)
      (Erdos922Recolor.maximalClique_attachments_anticomplete G
        (hK.isMaximalClique K) hdiamond hfour)
  have hchi : Erdos922FullB.chiNat G ≤ q + 1 :=
    (Erdos922FullB.colorable_iff_chiNat_le G (q + 1)).mp hcolor
  rw [hq] at hchi
  omega

/-- With the four-cycle part discharged by the even-hole contraction, only
the diamond exclusion is needed to obtain triangle-freeness. -/
theorem triangle_free_of_orderMinimal_of_noInducedDiamond
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (hdiamond : Erdos922Recolor.NoInducedDiamond G) :
    G.CliqueFree 3 := by
  classical
  exact triangle_free_of_orderMinimal G hmin hdiamond
    (noInducedFourCycle_of_orderMinimal G hmin)

/-- Every order-minimal counterexample is triangle-free. -/
theorem triangle_free_of_orderMinimalCounterexample
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G) :
    G.CliqueFree 3 := by
  classical
  exact triangle_free_of_orderMinimal G hmin
    (noInducedDiamond_of_orderMinimal G hmin)
    (noInducedFourCycle_of_orderMinimal G hmin)

end Erdos922Assembly
