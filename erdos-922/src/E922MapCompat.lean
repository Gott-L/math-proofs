/-
Lean 4.19 compatibility for the arbitrary-function simple-graph image used by
plby/lean-proofs Erdos922 at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
The mathematical definition deletes loops and keeps precisely the images of
original edges. This is a local implementation, not an assumption of contraction.
-/
import E922FiniteNext

namespace SimpleGraph

universe u v
variable {V : Type u} {W : Type v}

/-- Image through an arbitrary function, with all loops removed. -/
def mapFunctionCompat (G : SimpleGraph V) (f : V → W) : SimpleGraph W where
  Adj x y := x ≠ y ∧ ∃ a b, G.Adj a b ∧ f a = x ∧ f b = y
  symm := by
    rintro x y ⟨hne, a, b, hab, ha, hb⟩
    exact ⟨Ne.symm hne, b, a, hab.symm, hb, ha⟩
  loopless := by
    intro x h
    exact h.1 rfl

theorem mapFunctionCompat_adj_apply {G : SimpleGraph V} {f : V → W}
    {a b : V} (h : G.Adj a b) (hne : f a ≠ f b) :
    (G.mapFunctionCompat f).Adj (f a) (f b) :=
  ⟨hne, a, b, h, rfl, rfl⟩

end SimpleGraph
