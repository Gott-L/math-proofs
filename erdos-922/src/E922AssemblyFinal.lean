/-
Inherited finite Folkman proof from plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
Original informal mathematics: Jon Folkman; formal source: Codex / GPT-5.6 Sol.
Local Lean 4.19 compatibility and integration: Codex under Gott-L direction.
Private local work; upstream redistribution license unverified. No priority claim.
-/
import E922AssemblyStructural
import E922AssemblyChordless
import E922Attachments

namespace SimpleGraph

/-- Graph isomorphisms preserve the entire finite colorability predicate. -/
theorem chromaticNumber_congr {V W : Type*} {G : SimpleGraph V}
    {H : SimpleGraph W} (e : G ≃g H) : G.chromaticNumber = H.chromaticNumber := by
  have hcolor : G.Colorable = H.Colorable := by
    funext n
    apply propext
    constructor
    · rintro ⟨c⟩
      exact ⟨c.comp e.symm.toHom⟩
    · rintro ⟨c⟩
      exact ⟨c.comp e.toHom⟩
  simp only [chromaticNumber, hcolor]

end SimpleGraph

namespace Erdos922Assembly
open SimpleGraph
open scoped ENat
universe u

/-- The structural heart of Folkman's argument: a counterexample minimal in
vertex order cannot exist. -/
theorem not_orderMinimalCounterexample
    {V : Type u} [Fintype V] (G : SimpleGraph V) :
    ¬ Erdos922FullB.IsOrderMinimalCounterexample G := by
  classical
  intro hmin
  obtain ⟨v, w, hw, hlen⟩ := hmin.exists_shortest_cycle
  have hchord : w.IsChordless :=
    isChordless_of_isCycle_length_eq_girth hw hlen
  have hnoConfig : ¬ ∃ (A B : Finset V) (p : ℕ),
      Erdos922.EvenHole.Configuration G A B p :=
    Erdos922.EvenHole.no_configuration_of_orderMinimalCounterexample G hmin
  have hnoEven : Erdos922Recolor.NoInducedEvenCycleIso G :=
    Erdos922Recolor.EvenCycleBridge.no_induced_even_cycle_iso_of_no_configuration
      G hnoConfig
  have hnNotEven : ¬ Even w.length :=
    Erdos922Recolor.not_even_length_of_chordless_cycle G hnoEven w hw hchord
  have hnOdd : Odd w.length := Nat.not_even_iff_odd.mp hnNotEven
  have hn3 : w.length ≠ 3 := by
    intro hw3
    have hex : ∃ T, G.IsNClique 3 T :=
      SimpleGraph.is3Clique_iff_exists_cycle_length_three.mpr
        ⟨v, w, hw, hw3⟩
    obtain ⟨T, hT⟩ := hex
    exact triangle_free_of_orderMinimalCounterexample G hmin T hT
  have hn5 : 5 ≤ w.length := by
    obtain ⟨m, hm⟩ := hnOdd
    have := hw.three_le_length
    omega
  have hshort : Erdos922Recolor.IsShortestCycleLength G w.length := by
    intro z c hc
    rw [hlen]
    exact SimpleGraph.girth_le_length (G := G) hc
  obtain ⟨C, ⟨e⟩⟩ :=
    Erdos922Recolor.inducedCycleIso_of_chordless_cycle w hw hchord
  let X : Finset V := Finset.univ.filter fun x ↦ x ∈ C
  have hXset : (X : Set V) = C := by
    ext x
    simp [X]
  have hXnonempty : X.Nonempty := by
    let i : Fin w.length := ⟨0, by omega⟩
    let x : C := e.symm i
    refine ⟨x.1, ?_⟩
    simp [X, x.2]
  have hcoreChromatic : (G.induce C).chromaticNumber = 3 := by
    rw [SimpleGraph.chromaticNumber_congr e,
      SimpleGraph.chromaticNumber_cycleGraph_of_odd w.length (by omega) hnOdd]
  have hcoreChi : Erdos922FullB.chiNat (G.induce C) = 3 := by
    unfold Erdos922FullB.chiNat
    rw [hcoreChromatic]
    simp
  have hXproper : X ≠ (Finset.univ : Finset V) := by
    intro hXu
    have hCuniv : C = Set.univ := by
      rw [← hXset]
      ext x
      simp [hXu]
    have hinduceChi : Erdos922FullB.chiNat (G.induce Set.univ) =
        Erdos922FullB.chiNat G := by
      unfold Erdos922FullB.chiNat
      rw [SimpleGraph.chromaticNumber_congr (SimpleGraph.induceUnivIso G)]
    rw [hCuniv, hinduceChi] at hcoreChi
    have hfour := hmin.four_le_chiNat
    omega
  have hsplit := hmin.critical_split X hXnonempty hXproper
  rw [show ((↑(Xᶜ) : Set V)) = ((X : Set V)ᶜ) by ext x; simp] at hsplit
  rw [hXset] at hsplit
  let q : ℕ := Erdos922FullB.chiNat G - 2
  have hq : 2 ≤ q := by
    dsimp only [q]
    have hfour := hmin.four_le_chiNat
    omega
  have houtChi : Erdos922FullB.chiNat (G.induce Cᶜ) ≤ q := by
    dsimp only [q]
    omega
  obtain ⟨outsideColor⟩ : (G.induce Cᶜ).Colorable q :=
    (Erdos922FullB.colorable_iff_chiNat_le _ q).mpr houtChi
  have hunique : ∀ {r s : C}, r ≠ s → ∀ {x : V}, x ∉ C →
      G.Adj s.1 x → ¬ G.Adj r.1 x :=
    Erdos922Recolor.shortestCycle_attachment_unique G hn5 e hshort
  have hanti : ∀ {r s : C}, r ≠ s → ∀ {x y : V}, x ∉ C → y ∉ C →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y :=
    Erdos922Recolor.shortestOddCycle_attachments_anticomplete
      G hn5 hnOdd e hshort hnoEven hunique
  have hcolor : G.Colorable (q + 1) :=
    Erdos922Recolor.shortestCycle_final_recoloring_of_iso
      G q w.length C (by omega) hq e outsideColor hunique hanti
  have hchi : Erdos922FullB.chiNat G ≤ q + 1 :=
    (Erdos922FullB.colorable_iff_chiNat_le G (q + 1)).mp hcolor
  dsimp only [q] at hchi
  have hfour := hmin.four_le_chiNat
  omega

/-- There is no order-minimal counterexample. -/
theorem noOrderMinimalCounterexample :
    Erdos922FullB.NoOrderMinimalCounterexample.{u} := by
  intro V _ _ G
  exact not_orderMinimalCounterexample G

end Erdos922Assembly

namespace Erdos922

universe u

/-- Erdős Problem 922 (Folkman's theorem): the hereditary independent-set
hypothesis forces chromatic number at most `k + 2`. -/
theorem erdos_922 {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hG : HasLargeIndependentSets G k) :
    G.chromaticNumber ≤ ((k + 2 : ℕ) : ℕ∞) := by
  classical
  letI := Fintype.ofFinite V
  exact Erdos922Assembly.erdos_922_of_noOrderMinimalCounterexample
    Erdos922Assembly.noOrderMinimalCounterexample G k hG

end Erdos922
