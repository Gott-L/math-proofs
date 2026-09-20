/-
Inherited finite Folkman proof from plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
Original informal mathematics: Jon Folkman; formal source: Codex / GPT-5.6 Sol.
Local Lean 4.19 compatibility and integration: Codex under Gott-L direction.
Private local work; upstream redistribution license unverified. No priority claim.
-/
import E922ChordlessCompat
import E922AssemblyNumerics

namespace SimpleGraph

/-- Compatibility proof from the existing extended-girth infimum. -/
theorem girth_le_length {V : Type*} {G : SimpleGraph V}
    {v : V} {w : G.Walk v v} (hw : w.IsCycle) : G.girth ≤ w.length := by
  exact ENat.toNat_le_of_le_coe ((le_egirth (G := G)).mp le_rfl v w hw)

end SimpleGraph

namespace Erdos922Assembly

open SimpleGraph
open scoped ENat

universe u

variable {V : Type u} {G : SimpleGraph V}

theorem exists_shorter_cycle_of_chord
    {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    {x y : V} (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hxy : G.Adj x y) (hnot : ¬ c.toSubgraph.Adj x y) :
    ∃ a : V, ∃ c' : G.Walk a a, c'.IsCycle ∧ c'.length < c.length := by
  classical
  let r := c.rotate hx
  have hr_cycle : r.IsCycle := hc.rotate hx
  have hlen_rot : r.length = c.length := by
    have hlen1 :
        (c.takeUntil x hx).length + (c.dropUntil x hx).length = c.length := by
      have hlen1' := congrArg SimpleGraph.Walk.length
        (SimpleGraph.Walk.take_spec c hx)
      rw [SimpleGraph.Walk.length_append] at hlen1'
      exact hlen1'
    calc
      r.length = (c.dropUntil x hx).length + (c.takeUntil x hx).length := by
        simp [r, SimpleGraph.Walk.rotate, SimpleGraph.Walk.length_append]
      _ = (c.takeUntil x hx).length + (c.dropUntil x hx).length := by omega
      _ = c.length := hlen1
  have hy' : y ∈ r.support := by
    have hyv : y ∈ c.toSubgraph.verts := by
      simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using hy
    have : y ∈ r.toSubgraph.verts := by
      simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using hyv
    simpa [SimpleGraph.Walk.mem_verts_toSubgraph] using this
  let p := r.takeUntil y hy'
  have hp_path : p.IsPath := hr_cycle.isPath_takeUntil hy'
  have hnot_adj_r : ¬ r.toSubgraph.Adj x y := by
    simpa [r, SimpleGraph.Walk.toSubgraph_rotate] using hnot
  have hnot_edge_r : s(x, y) ∉ r.edges := by
    intro hmem
    have : r.toSubgraph.Adj x y := by
      have : s(x, y) ∈ r.toSubgraph.edgeSet :=
        (r.mem_edges_toSubgraph).2 hmem
      exact (SimpleGraph.Subgraph.mem_edgeSet
        (G' := r.toSubgraph) (v := x) (w := y)).1 this
    exact hnot_adj_r this
  have hnot_edge_p : s(x, y) ∉ p.edges := by
    intro hmem
    exact hnot_edge_r ((r.edges_takeUntil_subset hy') hmem)
  have hp_len_lt : p.length < r.length := by
    exact r.length_takeUntil_lt hy' (G.ne_of_adj hxy).symm
  have hlen_ne : p.length + 1 ≠ r.length := by
    intro hlen
    have hlen' : p.length = r.length - 1 := by omega
    have hget : r.getVert p.length = y := by
      have hpl : p.getVert p.length = y := by simp
      have hpr : p.getVert p.length = r.getVert p.length := by
        dsimp [p]
        exact r.getVert_takeUntil hy' (by rfl)
      exact hpr.symm.trans hpl
    have hpend : r.penultimate = y := by
      simpa [SimpleGraph.Walk.penultimate, hlen'] using hget
    have hadj_pen : r.toSubgraph.Adj r.penultimate x :=
      r.toSubgraph_adj_penultimate hr_cycle.not_nil
    have : r.toSubgraph.Adj x y := by
      have hsymm : r.toSubgraph.Adj x r.penultimate := hadj_pen.symm
      simpa [hpend] using hsymm
    exact hnot_adj_r this
  have hlen_short : p.length + 1 < r.length := by omega
  have hcyc' : (SimpleGraph.Walk.cons hxy.symm p).IsCycle := by
    have hnot_edge_p' : s(y, x) ∉ p.edges := by
      simpa [Sym2.eq_swap] using hnot_edge_p
    let pp : SimpleGraph.Path (G := G) x y := ⟨p, hp_path⟩
    exact SimpleGraph.Path.cons_isCycle (p := pp) (h := hxy.symm) hnot_edge_p'
  refine ⟨y, SimpleGraph.Walk.cons hxy.symm p, hcyc', ?_⟩
  simpa [SimpleGraph.Walk.length_cons, hlen_rot] using hlen_short

/-- A cycle attaining the girth has no chord. -/
theorem isChordless_of_isCycle_length_eq_girth
    {v : V} {w : G.Walk v v} (hw : w.IsCycle)
    (hlen : w.length = G.girth) : w.IsChordless := by
  classical
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
  intro x y hx hy hxy
  by_contra hedge
  have hnot : ¬ w.toSubgraph.Adj x y := by
    simpa only [SimpleGraph.Walk.adj_toSubgraph_iff_mem_edges] using hedge
  obtain ⟨a, w', hw', hshort⟩ :=
    exists_shorter_cycle_of_chord hw hx hy hxy hnot
  have hle := SimpleGraph.girth_le_length (G := G) hw'
  omega

end Erdos922Assembly
