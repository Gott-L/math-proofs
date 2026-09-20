import E922WalkCompat
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.Copy

/-!
A proved Lean4.19 cycle/copy compatibility interface for the inherited
Folkman/Erdos922 formalization. Written by Codex under Gott-L's direction.
The descending cycle walk follows the construction in Mathlib's Circulant.lean
(Iván Renison and Bhavik Mehta, Apache2.0); the path and containment arguments
below use its existing graph/walk APIs. No finite Folkman theorem is assumed.
-/

namespace SimpleGraph

universe u

private def descendingCycleWalk {n : ℕ} (hn : 0 < n) :
    (m : Fin n) → (cycleGraph n).Walk m ⟨0, hn⟩
  | ⟨0, _⟩ => .nil
  | ⟨m + 1, hm⟩ =>
    have ha : (cycleGraph n).Adj ⟨m + 1, hm⟩ ⟨m, by omega⟩ := by
      apply cycleGraph_adj'.mpr
      left
      rw [Fin.sub_val_of_le (by simp)]
      simp
    .cons ha (descendingCycleWalk hn ⟨m, by omega⟩)

private theorem descendingCycleWalk_length {n : ℕ} (hn : 0 < n) :
    ∀ m : Fin n, (descendingCycleWalk hn m).length = m.val
  | ⟨0, _⟩ => by simp [descendingCycleWalk]
  | ⟨m + 1, hm⟩ => by
    rw [descendingCycleWalk, Walk.length_cons, descendingCycleWalk_length]
termination_by m => m.val

private theorem descendingCycleWalk_mem_le {n : ℕ} (hn : 0 < n) :
    ∀ (m x : Fin n), x ∈ (descendingCycleWalk hn m).support → x.val ≤ m.val
  | ⟨0, _⟩, x, hx => by
    simp only [descendingCycleWalk, Walk.support_nil, List.mem_singleton] at hx
    subst x
    exact le_rfl
  | ⟨m + 1, hm⟩, x, hx => by
    simp only [descendingCycleWalk, Walk.support_cons, List.mem_cons] at hx
    rcases hx with hx | hx
    · subst x; exact le_rfl
    · have := descendingCycleWalk_mem_le hn ⟨m, by omega⟩ x hx
      simp only [Fin.val_mk] at this ⊢
      omega

private theorem descendingCycleWalk_isPath {n : ℕ} (hn : 0 < n) :
    ∀ m : Fin n, (descendingCycleWalk hn m).IsPath
  | ⟨0, _⟩ => by simp only [descendingCycleWalk]; exact Walk.IsPath.nil
  | ⟨m + 1, hm⟩ => by
    rw [descendingCycleWalk]
    apply Walk.IsPath.cons (descendingCycleWalk_isPath hn ⟨m, by omega⟩)
    intro hx
    have := descendingCycleWalk_mem_le hn ⟨m, by omega⟩ ⟨m + 1, hm⟩ hx
    simp only [Fin.val_mk] at this
    omega

private theorem cycleGraph_cycle (m : ℕ) :
    ∃ w : (cycleGraph (m + 3)).Walk 0 0, w.IsCycle ∧ w.length = m + 3 := by
  have hn : 0 < m + 3 := by omega
  let p := descendingCycleWalk hn (Fin.last (m + 2))
  have ha : (cycleGraph (m + 3)).Adj 0 (Fin.last (m + 2)) := by
    simp [cycleGraph_adj]
  let w := p.cons ha
  have hwlen : w.length = m + 3 := by
    simp only [w, Walk.length_cons, p, descendingCycleWalk_length, Fin.val_last]
  refine ⟨w, ?_, hwlen⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨?_, by omega⟩
  simpa only [w, Walk.tail_cons, Walk.isPath_copy] using
    descendingCycleWalk_isPath hn (Fin.last (m + 2))

private theorem cycle_copy_of_walk {V : Type u} {G : SimpleGraph V}
    {v : V} (w : G.Walk v v) (hw : w.IsCycle) :
    Nonempty (Copy (cycleGraph w.length) G) := by
  have hstep (i j : Fin w.length) (hij : (j - i).val = 1) :
      G.Adj (w.getVert i.val) (w.getVert j.val) := by
    by_cases hijle : i ≤ j
    · rw [Fin.sub_val_of_le hijle] at hij
      have hji : j.val = i.val + 1 := by omega
      rw [hji]
      exact w.adj_getVert_succ i.isLt
    · have hji : j < i := lt_of_not_ge hijle
      rw [Fin.coe_sub_iff_lt.mpr hji] at hij
      have hi : i.val + 1 = w.length := by omega
      have hj : j.val = 0 := by omega
      have he := w.adj_getVert_succ i.isLt
      rw [hi, Walk.getVert_length] at he
      simpa only [hj, Walk.getVert_zero] using he
  refine ⟨⟨⟨(fun i : Fin w.length => w.getVert i.val), ?_⟩, ?_⟩⟩
  · intro i j hij
    rcases cycleGraph_adj'.mp hij with hij | hij
    · exact (hstep j i hij).symm
    · exact hstep i j hij
  · intro i j hij
    apply Fin.ext
    exact hw.getVert_injOn' (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) hij

/-- A copy of a cycle graph of order at least three is exactly a simple cycle
walk of that length. This includes both directions required by the public proof. -/
theorem cycleGraph_isContained_iff {V : Type u} {G : SimpleGraph V}
    {n : ℕ} (hn : 2 < n) :
    cycleGraph n ⊑ G ↔ ∃ (v : V) (w : G.Walk v v), w.IsCycle ∧ w.length = n := by
  constructor
  · rintro ⟨f⟩
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 3 := ⟨n - 3, by omega⟩
    obtain ⟨w, hw, hlen⟩ := cycleGraph_cycle m
    exact ⟨f 0, w.map f.toHom, hw.map f.injective, by simpa using hlen⟩
  · rintro ⟨v, w, hw, hlen⟩
    subst n
    exact cycle_copy_of_walk w hw

end SimpleGraph
