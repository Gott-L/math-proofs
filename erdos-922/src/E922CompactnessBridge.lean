import E922LocalTransfer
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions

/-!
A conditional finite-to-infinite bridge for Erdos--Hajnal 922 / Folkman's
theorem. This file does NOT provide the finite Folkman theorem.

The compactness argument is the standard de Bruijn--Erdos argument, here
implemented using Mathlib's existing Tychonoff and closed-intersection
theorems to avoid rebuilding an unavailable category-theoretic interface.
Folkman, Erdos--Hajnal, the modern finite-proof authors, and Mathlib's authors
retain their mathematical/formalization credit. New glue implementation:
Codex under Gott-L's direction. No public finite-proof code is copied here.
-/

namespace Erdos922Adapter

universe u

/-- A fixed finite palette suffices globally if it suffices on every induced
finite vertex set. No finiteness, countability, or local-finiteness assumption
is made about the original graph. -/
theorem colorable_of_finite_restrictions
    {V : Type u} (G : SimpleGraph V) (n : ℕ) (hn : 0 < n)
    (hfinite : ∀ S : Finset V, (finiteRestriction G S).Colorable n) :
    G.Colorable n := by
  classical
  letI : TopologicalSpace (Fin n) := ⊥
  letI : DiscreteTopology (Fin n) := ⟨rfl⟩
  let C : V × V → Set (V → Fin n) :=
    fun e => {f | G.Adj e.1 e.2 → f e.1 ≠ f e.2}
  have hclosed : ∀ e, IsClosed (C e) := by
    intro e
    by_cases he : G.Adj e.1 e.2
    · have hcont : Continuous (fun f : V → Fin n => (f e.1, f e.2)) :=
        (continuous_apply e.1).prodMk (continuous_apply e.2)
      simpa only [C, he, true_implies] using
        (isClosed_discrete {p : Fin n × Fin n | p.1 ≠ p.2}).preimage
          hcont
    · simp [C, he]
  have hfin : ∀ t : Finset (V × V),
      (Set.univ ∩ ⋂ e ∈ t, C e).Nonempty := by
    intro t
    let S : Finset V := t.image Prod.fst ∪ t.image Prod.snd
    let c := Classical.choice (hfinite S)
    let f : V → Fin n := fun v => if hv : v ∈ S then c ⟨v, hv⟩ else ⟨0, hn⟩
    refine ⟨f, Set.mem_univ _, ?_⟩
    apply Set.mem_iInter.mpr
    intro e
    apply Set.mem_iInter.mpr
    intro he
    have hleft : e.1 ∈ S := Finset.mem_union_left _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    have hright : e.2 ∈ S := Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    change G.Adj e.1 e.2 → f e.1 ≠ f e.2
    intro hadj
    have hc := c.valid (show (finiteRestriction G S).Adj ⟨e.1, hleft⟩ ⟨e.2, hright⟩ from hadj)
    simpa only [f, dif_pos hleft, dif_pos hright] using hc
  obtain ⟨f, _, hf⟩ := isCompact_univ.inter_iInter_nonempty C hclosed hfin
  refine ⟨SimpleGraph.Coloring.mk f ?_⟩
  intro a b hab
  exact (Set.mem_iInter.mp hf (a, b)) hab

/-- Conditional integration only: an actual finite Folkman supplier is an
explicit premise. This theorem is not the full Folkman theorem by itself. -/
theorem colorable_of_finite_folkman
    {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (finiteFolkman : ∀ (W : Type u) [Finite W] (H : SimpleGraph W),
      LargeIndependentFinsets H k → H.Colorable (k + 2))
    (hG : LargeIndependentFinsets G k) : G.Colorable (k + 2) := by
  apply colorable_of_finite_restrictions G (k + 2) (by omega)
  intro S
  exact finiteFolkman {v // v ∈ S} (finiteRestriction G S) (hG.finiteRestriction S)

/-- The corresponding chromatic-number conclusion, with the SAME explicit
finite-theorem premise; the finite supplier is not constructed in this file. -/
theorem chromaticNumber_le_of_finite_folkman
    {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (finiteFolkman : ∀ (W : Type u) [Finite W] (H : SimpleGraph W),
      LargeIndependentFinsets H k → H.Colorable (k + 2))
    (hG : LargeIndependentFinsets G k) : G.chromaticNumber ≤ k + 2 := by
  exact (colorable_of_finite_folkman G k finiteFolkman hG).chromaticNumber_le

end Erdos922Adapter

#print axioms Erdos922Adapter.colorable_of_finite_restrictions
#print axioms Erdos922Adapter.colorable_of_finite_folkman
#print axioms Erdos922Adapter.chromaticNumber_le_of_finite_folkman
