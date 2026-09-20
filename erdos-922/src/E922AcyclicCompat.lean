import E922ParityCompat

/-!
The classical two-colorability of a forest, constructed from unique paths
to a selected root in each component. This proof uses Mathlib4.19's proved
path-uniqueness theorem, not an assumed coloring or Folkman supplier.
Gott-L directed the project; Codex/C wrote this compatibility proof.
-/

namespace SimpleGraph

universe u
variable {V : Type u} {G : SimpleGraph V}

private theorem acyclic_path_length_adj (hG : G.IsAcyclic)
    {r v w : V} (hvw : G.Adj v w) (p : G.Path v r) (q : G.Path w r) :
    p.val.length = q.val.length + 1 ∨ q.val.length = p.val.length + 1 := by
  classical
  by_cases hv : v ∈ q.val.support
  · have ht := hG.path_unique
      (⟨q.val.takeUntil v hv, q.property.takeUntil hv⟩ : G.Path w v)
      (Path.singleton hvw.symm)
    have hd := hG.path_unique
      (⟨q.val.dropUntil v hv, q.property.dropUntil hv⟩ : G.Path v r) p
    have htl := congrArg (fun z : G.Path w v => z.val.length) ht
    have hdl := congrArg (fun z : G.Path v r => z.val.length) hd
    have hsum := congrArg Walk.length (q.val.take_spec hv)
    simp only [Walk.length_append] at hsum
    simp only [Path.singleton, Walk.length_cons, Walk.length_nil] at htl
    change (q.val.takeUntil v hv).length = 1 at htl
    change (q.val.dropUntil v hv).length = p.val.length at hdl
    right
    simpa only [htl, hdl, Nat.add_comm] using hsum.symm
  · have hp := hG.path_unique p
      (⟨Walk.cons hvw q.val, q.property.cons hv⟩ : G.Path v r)
    have hlen := congrArg (fun z : G.Path v r => z.val.length) hp
    exact Or.inl (by simpa only [Walk.length_cons] using hlen)

theorem IsAcyclic.colorable_two (hG : G.IsAcyclic) : G.Colorable 2 := by
  classical
  let root : G.ConnectedComponent → V := fun c => c.out
  have hr (v : V) : G.Reachable v (root (G.connectedComponentMk v)) := by
    apply ConnectedComponent.exact
    exact (G.connectedComponentMk v).out_eq.symm
  let path (v : V) : G.Path v (root (G.connectedComponentMk v)) :=
    (hr v).some.toPath
  let color (v : V) : Fin 2 :=
    ⟨(path v).val.length % 2, Nat.mod_lt _ (by decide)⟩
  refine ⟨Coloring.mk color ?_⟩
  intro v w hvw he
  have hc : (path v).val.length % 2 = (path w).val.length % 2 := congrArg Fin.val he
  have heq : root (G.connectedComponentMk v) = root (G.connectedComponentMk w) :=
    congrArg root (ConnectedComponent.connectedComponentMk_eq_of_adj hvw)
  let qw : G.Path w (root (G.connectedComponentMk v)) :=
    ⟨(path w).val.copy rfl heq.symm,
      (Walk.isPath_copy _ _ _).mpr (path w).property⟩
  have hlen := acyclic_path_length_adj hG hvw (path v) qw
  simp only [qw, Walk.length_copy] at hlen
  omega

theorem IsAcyclic.even_loop_length (hG : G.IsAcyclic)
    (v : V) (p : G.Walk v v) : Even p.length :=
  two_colorable_iff_forall_loop_even.mp hG.colorable_two v p

end SimpleGraph
