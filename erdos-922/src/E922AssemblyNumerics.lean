/-
Inherited finite Folkman proof from plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
Original informal mathematics: Jon Folkman; formal source: Codex / GPT-5.6 Sol.
Local Lean 4.19 compatibility and integration: Codex under Gott-L direction.
Private local work; upstream redistribution license unverified. No priority claim.
-/
import E922EvenCycleBridgeUse

namespace Erdos922Assembly
open SimpleGraph
open scoped ENat
universe u

theorem fOn_le_of_large_independent_sets
    {V : Type u} [Fintype V] {G : SimpleGraph V} {k : ℕ}
    (hG : Erdos922.HasLargeIndependentSets G k) :
    Erdos922FullB.fOn G Finset.univ ≤ (k : ℤ) := by
  classical
  obtain ⟨S, -, hSf⟩ :=
    Erdos922FullB.exists_maximum_potential_on G (Finset.univ : Finset V)
  rw [← hSf]
  obtain ⟨I, hIS, hI, hcard⟩ := hG.onFinsets S
  have hIa : I.card ≤ Erdos922FullB.alphaOn G S :=
    Erdos922FullB.card_le_alphaOn hIS hI
  simp only [Erdos922FullB.potential]
  omega

theorem erdos_922_of_noOrderMinimalCounterexample
    {V : Type u} [Finite V]
    (hNo : Erdos922FullB.NoOrderMinimalCounterexample.{u})
    (G : SimpleGraph V) (k : ℕ)
    (hG : Erdos922.HasLargeIndependentSets G k) :
    G.chromaticNumber ≤ ((k + 2 : ℕ) : ℕ∞) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hfolk : Erdos922FullB.FolkmanBound G :=
    Erdos922FullB.folkmanBound_of_noOrderMinimalCounterexample hNo G
  have hf : Erdos922FullB.fOn G Finset.univ ≤ (k : ℤ) :=
    fOn_le_of_large_independent_sets hG
  have hnonneg := Erdos922FullB.fOn_nonneg G (Finset.univ : Finset V)
  have hnat : Int.toNat (Erdos922FullB.fOn G Finset.univ) ≤ k := by omega
  rw [SimpleGraph.chromaticNumber_le_iff_colorable]
  exact SimpleGraph.Colorable.mono (Nat.add_le_add_right hnat 2) hfolk

/-- On a nonempty clique, the largest independent subset has exactly one
vertex.  This tiny estimate is the numerical input used at the maximum
clique in the final recoloring argument. -/
theorem alphaOn_eq_one_of_nonempty_clique
    {V : Type u} {G : SimpleGraph V} {K : Finset V}
    (hK : G.IsClique (K : Set V)) (hKne : K.Nonempty) :
    Erdos922FullB.alphaOn G K = 1 := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨I, hIK, hI, hIcard⟩ :=
      Erdos922FullB.exists_maximum_independent_subset G K
    rw [← hIcard]
    apply Finset.card_le_one.mpr
    intro a ha b hb
    by_contra hab
    exact hI ha hb hab (hK (hIK ha) (hIK hb) hab)
  · obtain ⟨v, hv⟩ := hKne
    have hsind : G.IsIndepSet ({v} : Finset V) := by simp
    simpa using Erdos922FullB.card_le_alphaOn
      (G := G) (I := ({v} : Finset V)) (S := K)
      (by simpa using hv) hsind

/-- The two bipartition classes of an induced four-cycle satisfy the exact
abstract configuration consumed by the even-hole contraction argument. -/
theorem evenHoleConfiguration_of_inducedFourCycle
    {V : Type u} [DecidableEq V] {G : SimpleGraph V} {a b c d : V}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hAB : G.Adj a b) (hBC : G.Adj b c)
    (hCD : G.Adj c d) (hDA : G.Adj d a)
    (hAC : ¬ G.Adj a c) (hBD : ¬ G.Adj b d) :
    Erdos922.EvenHole.Configuration G ({a, c} : Finset V)
      ({b, d} : Finset V) 2 := by
  classical
  refine ⟨?_, by omega, by simp [hac], by simp [hbd], ?_, ?_, ?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [Finset.mem_insert, Finset.mem_singleton] at hxA hxB
    rcases hxA with rfl | rfl <;> rcases hxB with rfl | rfl <;> contradiction
  · intro x hx y hy hxy
    change x ∈ ({a, c} : Finset V) at hx
    change y ∈ ({a, c} : Finset V) at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals first | exact (hxy rfl).elim | exact hAC | exact fun h ↦ hAC h.symm
  · intro x hx y hy hxy
    change x ∈ ({b, d} : Finset V) at hx
    change y ∈ ({b, d} : Finset V) at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    all_goals first | exact (hxy rfl).elim | exact hBD | exact fun h ↦ hBD h.symm
  · intro I hsub hI
    by_contra hnot
    have hlt : 2 < I.card := by omega
    obtain ⟨x, y, z, hxI, hyI, hzI, hxy, hxz, hyz⟩ :=
      Finset.two_lt_card_iff.mp hlt
    have hnxy : ¬ G.Adj x y := hI hxI hyI hxy
    have hnxz : ¬ G.Adj x z := hI hxI hzI hxz
    have hnyz : ¬ G.Adj y z := hI hyI hzI hyz
    have hnyx : ¬ G.Adj y x := fun h ↦ hnxy h.symm
    have hnzx : ¬ G.Adj z x := fun h ↦ hnxz h.symm
    have hnzy : ¬ G.Adj z y := fun h ↦ hnyz h.symm
    have hxC := hsub hxI
    have hyC := hsub hyI
    have hzC := hsub hzI
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hxC hyC hzC
    rcases hxC with (rfl | rfl) | (rfl | rfl) <;>
      rcases hyC with (rfl | rfl) | (rfl | rfl) <;>
      rcases hzC with (rfl | rfl) | (rfl | rfl)
    all_goals simp_all
  · intro I hsub hI hcard
    obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hcard
    have hxC := hsub (Finset.mem_insert_self x {y})
    have hyMem : y ∈ ({x, y} : Finset V) := by simp
    have hyC := hsub hyMem
    have hnxy : ¬ G.Adj x y := hI (by simp) (by simp) hxy
    have hnyx : ¬ G.Adj y x := fun h ↦ hnxy h.symm
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hxC hyC
    rcases hxC with (rfl | rfl) | (rfl | rfl) <;>
      rcases hyC with (rfl | rfl) | (rfl | rfl)
    all_goals simp_all [Finset.pair_comm]

end Erdos922Assembly
