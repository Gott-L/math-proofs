import E922FiniteBase
import E922LocalTransfer

/-!
Exact definition bridge between the independently written local compactness
interface and the preserved public finite Folkman definitions. This supplies
no finite Folkman theorem. Written by Codex under Gott-L's direction; the
public predicates and their finite equivalence retain the upstream credits.
-/

namespace Erdos922Adapter

universe u

theorem localCondition_iff_publicFinsets {V : Type u}
    (G : SimpleGraph V) (k : ℕ) :
    LargeIndependentFinsets G k ↔
      Erdos922.HasLargeIndependentSetsOnFinsets G k := Iff.rfl

theorem localCondition_iff_publicSubgraphs {V : Type u} [Finite V]
    (G : SimpleGraph V) (k : ℕ) :
    LargeIndependentFinsets G k ↔ Erdos922.HasLargeIndependentSets G k :=
  (localCondition_iff_publicFinsets G k).trans
    Erdos922.hasLargeIndependentSets_iff_onFinsets.symm

end Erdos922Adapter
