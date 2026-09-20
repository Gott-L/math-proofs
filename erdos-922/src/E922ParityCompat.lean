import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Coloring

/-!
Classical two-coloring and parity interfaces proved in the existing Lean4.19
library. Gott-L directed the compatibility project; Codex/C constructed this
proof using the existing Mathlib walk, component, coloring and parity APIs.
This supplies no finite Folkman bound. The upstream E922 formalization and
Mathlib authors retain their original credit.
-/

namespace SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}

private theorem color_value_walk_parity (c : G.Coloring (Fin 2))
    {v w : V} (p : G.Walk v w) :
    ((c v).val + p.length) % 2 = (c w).val := by
  induction p with
  | nil => simp [Nat.mod_eq_of_lt (c _).isLt]
  | @cons a b z h p ih =>
    have ha := (c a).isLt
    have hb := (c b).isLt
    have hn : (c a).val ≠ (c b).val := fun he => c.valid h (Fin.ext he)
    simp only [Walk.length_cons]
    omega

theorem two_colorable_iff_forall_loop_even :
    G.Colorable 2 ↔ ∀ (v : V) (p : G.Walk v v), Even p.length := by
  classical
  constructor
  · rintro ⟨c⟩ v p
    have hp := color_value_walk_parity c p
    have hv := (c v).isLt
    apply Nat.even_iff.mpr
    omega
  · intro h
    let root : G.ConnectedComponent → V := fun c => c.out
    have hr (v : V) : G.Reachable (root (G.connectedComponentMk v)) v := by
      apply ConnectedComponent.exact
      exact (G.connectedComponentMk v).out_eq
    let path (v : V) : G.Walk (root (G.connectedComponentMk v)) v :=
      (hr v).some
    let color (v : V) : Fin 2 := ⟨(path v).length % 2, Nat.mod_lt _ (by decide)⟩
    refine ⟨Coloring.mk color ?_⟩
    intro v w hvw he
    have hc : (path v).length % 2 = (path w).length % 2 := congrArg Fin.val he
    have heq : root (G.connectedComponentMk v) = root (G.connectedComponentMk w) :=
      congrArg root (ConnectedComponent.connectedComponentMk_eq_of_adj hvw)
    let pv : G.Walk (root (G.connectedComponentMk w)) v :=
      (path v).copy heq rfl
    let loop := (pv.concat hvw).append (path w).reverse
    have heven := h _ loop
    have hmod := Nat.even_iff.mp heven
    simp only [loop, Walk.length_append, Walk.length_concat, Walk.length_reverse,
      pv, Walk.length_copy] at hmod
    omega

end SimpleGraph
