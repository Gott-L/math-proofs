import E922AssemblyFinal
import E922FiniteSubgraphInterface
import E922CompactnessBridge

/-!
Integration of the supplied finite Folkman theorem with finite-coloring
compactness. The mathematical theorem is Folkman's; the compactness argument
is classical. The finite proof retains the upstream formal authors' credit.
This local integration was written by Codex under Gott-L's project direction.
No historical-priority or award-eligibility assertion is made.
-/

open scoped ENat

namespace Erdos922Adapter

universe u

/-- The actual finite theorem supplies the palette on every finite vertex
type. There is no minimal-counterexample or finite-theorem premise. -/
theorem finite_colorable_of_largeIndependentFinsets
    {V : Type u} [Finite V] (G : SimpleGraph V) (k : ℕ)
    (hG : LargeIndependentFinsets G k) : G.Colorable (k + 2) := by
  exact SimpleGraph.chromaticNumber_le_iff_colorable.mp
    (Erdos922.erdos_922 G k ((localCondition_iff_publicSubgraphs G k).mp hG))

/-- Folkman's bound for arbitrary graphs under the finite-local hypothesis.
No finiteness, countability, or local-finiteness condition is imposed on V. -/
theorem colorable_of_largeIndependentFinsets
    {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (hG : LargeIndependentFinsets G k) : G.Colorable (k + 2) := by
  exact colorable_of_finite_folkman G k
    (fun W _ H hH => finite_colorable_of_largeIndependentFinsets H k hH) hG

theorem chromaticNumber_le_of_largeIndependentFinsets
    {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (hG : LargeIndependentFinsets G k) :
    G.chromaticNumber ≤ ((k + 2 : ℕ) : ℕ∞) :=
  (colorable_of_largeIndependentFinsets G k hG).chromaticNumber_le

/-- Literal finite-subgraph formulation, allowing edge-deleted subgraphs
and an arbitrary ambient vertex type. -/
theorem colorable_of_largeIndependentFiniteSubgraphs
    {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (hG : LargeIndependentFiniteSubgraphs G k) : G.Colorable (k + 2) :=
  colorable_of_largeIndependentFinsets G k
    ((localCondition_iff_finiteSubgraphs G k).mpr hG)

theorem chromaticNumber_le_of_largeIndependentFiniteSubgraphs
    {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (hG : LargeIndependentFiniteSubgraphs G k) :
    G.chromaticNumber ≤ ((k + 2 : ℕ) : ℕ∞) :=
  (colorable_of_largeIndependentFiniteSubgraphs G k hG).chromaticNumber_le

end Erdos922Adapter

namespace Erdos922

universe u

/-- Arbitrary-graph version in the inherited public finset terminology. -/
theorem erdos_922_arbitrary {V : Type u} (G : SimpleGraph V) (k : ℕ)
    (hG : HasLargeIndependentSetsOnFinsets G k) :
    G.chromaticNumber ≤ ((k + 2 : ℕ) : ℕ∞) := by
  exact Erdos922Adapter.chromaticNumber_le_of_largeIndependentFinsets G k
    ((Erdos922Adapter.localCondition_iff_publicFinsets G k).mpr hG)

end Erdos922
