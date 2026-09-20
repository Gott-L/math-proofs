import E922WalkCompat
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
Local Lean 4.19 compatibility for the finite Folkman proof's later walk API.
Gott-L directed the project; Codex constructed these compatibility proofs.
The original mathematics is Jon Folkman's; the inherited public formalization
is credited to Codex/GPT-5.6 Sol. No finite Folkman conclusion is assumed here.
The public source's repository license has not been confirmed; local use only.
-/

namespace SimpleGraph.Walk
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- A walk is chordless when every ambient edge on its support is one of its edges. -/
def IsChordless {a b : V} (p : G.Walk a b) : Prop :=
  ∀ x y, x ∈ p.support → y ∈ p.support → G.Adj x y → s(x, y) ∈ p.edges

theorem isChordless_iff_forall_mem_edges {a b : V} {p : G.Walk a b} :
    p.IsChordless ↔ ∀ x y, x ∈ p.support → y ∈ p.support →
      G.Adj x y → s(x, y) ∈ p.edges := Iff.rfl

theorem IsChordless.mem_edges {a b x y : V} {p : G.Walk a b}
    (hp : p.IsChordless) (hx : x ∈ p.support) (hy : y ∈ p.support)
    (hxy : G.Adj x y) : s(x, y) ∈ p.edges := hp x y hx hy hxy

theorem IsPath.length_eq_one_of_mem_edges {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) (he : s(a, b) ∈ p.edges) : p.length = 1 := by
  have hlt : p.length < 2 := by
    by_contra h
    exact hp.not_mem_endpoint_edge_of_two_le (by omega) he
  have hne : p.length ≠ 0 := by
    intro h
    have hn := nil_iff_length_eq.mpr h
    cases p with
    | nil => simp at he
    | cons h q => exact not_nil_cons hn
  omega

theorem mk_mem_edges_iff_exists {a b x y : V} (p : G.Walk a b) :
    s(x, y) ∈ p.edges ↔ ∃ k, k < p.length ∧
      s(p.getVert k, p.getVert (k + 1)) = s(x, y) := by
  induction p with
  | nil => simp
  | @cons a c b hac p ih =>
    constructor
    · intro he
      rcases List.mem_cons.mp he with he | he
      · refine ⟨0, by simp, ?_⟩
        simpa using he.symm
      · obtain ⟨k, hk, he⟩ := ih.mp he
        exact ⟨k + 1, by simpa using hk, by simpa using he⟩
    · rintro ⟨k, hk, he⟩
      cases k with
      | zero => exact List.mem_cons.mpr (Or.inl (by simpa using he.symm))
      | succ k =>
        apply List.mem_cons.mpr
        right
        exact ih.mpr ⟨k, by simpa using hk, by simpa using he⟩

section
variable [DecidableEq V]

theorem edges_takeUntil_subset_edges {a b x : V} (p : G.Walk a b)
    (hx : x ∈ p.support) : (p.takeUntil x hx).edges ⊆ p.edges :=
  p.edges_takeUntil_subset hx

theorem edges_dropUntil_subset_edges {a b x : V} (p : G.Walk a b)
    (hx : x ∈ p.support) : (p.dropUntil x hx).edges ⊆ p.edges :=
  p.edges_dropUntil_subset hx

theorem length_takeUntil_le_length {a b x : V} (p : G.Walk a b)
    (hx : x ∈ p.support) : (p.takeUntil x hx).length ≤ p.length :=
  p.length_takeUntil_le hx

theorem length_dropUntil_le_length {a b x : V} (p : G.Walk a b)
    (hx : x ∈ p.support) : (p.dropUntil x hx).length ≤ p.length :=
  p.length_dropUntil_le hx

theorem length_takeUntil_lt_length {a b x : V} (p : G.Walk a b)
    (hx : x ∈ p.support) (hxb : x ≠ b) : (p.takeUntil x hx).length < p.length :=
  length_takeUntil_lt hx hxb

theorem mem_support_rotate_iff {a r w : V} (p : G.Walk a a)
    (hr : r ∈ p.support) : w ∈ (p.rotate hr).support ↔ w ∈ p.support := by
  rw [← mem_verts_toSubgraph, toSubgraph_rotate, mem_verts_toSubgraph]

@[simp] theorem length_rotate {a r : V} (p : G.Walk a a)
    (hr : r ∈ p.support) : (p.rotate hr).length = p.length := by
  have h := congrArg Walk.length (p.take_spec hr)
  simpa only [rotate, length_append, Nat.add_comm] using h

end

theorem adj_toSubgraph_iff_mem_edges {a b x y : V} (p : G.Walk a b) :
    p.toSubgraph.Adj x y ↔ s(x, y) ∈ p.edges := by
  change s(x, y) ∈ p.toSubgraph.edgeSet ↔ s(x, y) ∈ p.edges
  exact p.mem_edges_toSubgraph

end SimpleGraph.Walk
