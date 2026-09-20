import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card

/-!
A small hereditary transport interface for the finite-local hypothesis of
Erdos--Hajnal Problem 922 / Folkman's theorem. This file does not claim to
prove Folkman's finite theorem or its infinite-graph conclusion.

The mathematical result belongs to Folkman; the intended compactness step
is the standard de Bruijn--Erdos theorem. This new elementary transport proof
was written by Codex under Gott-L's direction, without copying the public
Erdos922 formalization. It uses only the already available Lean 4.19 modules.
-/

namespace Erdos922Adapter

universe u v

/-- The literal finite-vertex-set hypothesis, with independence written out
to avoid an unavailable graph-clique import in this bounded experiment. -/
def LargeIndependentFinsets {V : Type u} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, ∃ I : Finset V, I ⊆ S ∧
    (∀ a ∈ I, ∀ b ∈ I, a ≠ b → ¬ G.Adj a b) ∧ S.card ≤ 2 * I.card + k

/-- The hereditary condition transports to every graph with an injective
adjacency-preserving map into the original graph. In particular, deleting
edges cannot invalidate the local independent-set hypothesis. -/
theorem LargeIndependentFinsets.pullback
    {V : Type u} {W : Type v} {G : SimpleGraph V} {H : SimpleGraph W}
    {k : ℕ} (hG : LargeIndependentFinsets G k)
    (f : W → V) (hf : Function.Injective f)
    (hAdj : ∀ {a b : W}, H.Adj a b → G.Adj (f a) (f b)) :
    LargeIndependentFinsets H k := by
  classical
  intro S
  obtain ⟨I, hIS, hI, hcard⟩ := hG (S.image f)
  let J := S.filter fun x => f x ∈ I
  have hJ : J ⊆ S := Finset.filter_subset _ _
  have hImage : J.image f = I := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hy).2
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp (hIS hx)
      exact Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨hy, hx⟩, rfl⟩
  have hJcard : J.card = I.card := by
    rw [← hImage, Finset.card_image_of_injective _ hf]
  refine ⟨J, hJ, ?_, ?_⟩
  · intro a ha b hb hab hadj
    exact hI (f a) (Finset.mem_filter.mp ha).2
      (f b) (Finset.mem_filter.mp hb).2 (fun heq => hab (hf heq)) (hAdj hadj)
  · simpa only [Finset.card_image_of_injective _ hf, ← hJcard] using hcard

/-- The graph induced on a specified finite vertex set. This explicit
definition agrees with the usual induced-subgraph adjacency. -/
def finiteRestriction {V : Type u} (G : SimpleGraph V) (S : Finset V) :
    SimpleGraph {v // v ∈ S} where
  Adj a b := G.Adj a.val b.val
  symm := fun _ _ h => G.symm h
  loopless a := G.loopless a.val

theorem LargeIndependentFinsets.finiteRestriction
    {V : Type u} {G : SimpleGraph V} {k : ℕ}
    (hG : LargeIndependentFinsets G k) (S : Finset V) :
    LargeIndependentFinsets (finiteRestriction G S) k := by
  exact hG.pullback Subtype.val Subtype.val_injective (fun h => h)

end Erdos922Adapter

#print axioms Erdos922Adapter.LargeIndependentFinsets.pullback
#print axioms Erdos922Adapter.LargeIndependentFinsets.finiteRestriction
