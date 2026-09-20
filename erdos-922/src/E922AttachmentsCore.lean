/-
Inherited Erdos922 attachment and shortest-cycle arguments.
Source plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos922.lean, SHA256
0bc22004ecbe76ab3cc3f263c29c76994b39017828ea835d987139fa324b9971.
Informal author: Jon Folkman. Formal authors: Codex; GPT-5.6 Sol.
Lean4.19 compatibility work by Codex/B under Gott-L's direction.
Private local research; upstream license unverified; no novelty claim.
-/
import E922EvenCycleBridgeUse

open SimpleGraph
open scoped ENat

namespace Erdos922Recolor
universe u
variable {V : Type u}

/-- A local adjacency-pattern formulation of having no induced diamond
(`K₄` with one edge removed).  The explicit distinctness fields make the
definition robust when used independently of a surrounding vertex set. -/
def NoInducedDiamond (G : SimpleGraph V) : Prop :=
  ∀ {a b c d : V},
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    G.Adj a b → G.Adj a c → G.Adj b c →
    G.Adj a d → G.Adj b d → ¬ G.Adj c d → False

/-- A local adjacency-pattern formulation of having no induced four-cycle. -/
def NoInducedFourCycle (G : SimpleGraph V) : Prop :=
  ∀ {a b c d : V},
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
    ¬ G.Adj a c → ¬ G.Adj b d → False

/-- A vertex outside a maximal clique misses some vertex of that clique. -/
theorem exists_not_adj_of_maximal_clique
    (G : SimpleGraph V) {K : Set V} (hK : Maximal G.IsClique K)
    {x : V} (hx : x ∉ K) : ∃ y ∈ K, ¬ G.Adj y x := by
  by_contra h
  push_neg at h
  have hins : G.IsClique (insert x K) := by
    intro a ha b hb hab
    simp only [Set.mem_insert_iff] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact (hab rfl).elim
    · exact (h b hb).symm
    · exact h a ha
    · exact hK.1 ha hb hab
  have hsub : insert x K ⊆ K := hK.2 hins (Set.subset_insert x K)
  exact hx (hsub (Set.mem_insert x K))

/-- In a diamond-free graph, every outside vertex has at most one neighbor in
a maximal clique. -/
theorem maximalClique_attachment_unique
    (G : SimpleGraph V) {K : Set V} (hK : Maximal G.IsClique K)
    (hdiamond : NoInducedDiamond G) :
    ∀ {r s : K}, r ≠ s → ∀ {x : V}, x ∉ K →
      G.Adj s.1 x → ¬ G.Adj r.1 x := by
  intro r s hrs x hx hsx hrx
  obtain ⟨t, htK, htx⟩ := exists_not_adj_of_maximal_clique G hK hx
  have hrs' : r.1 ≠ s.1 := fun h ↦ hrs (Subtype.ext h)
  have hrt : r.1 ≠ t := fun h ↦ htx (h ▸ hrx)
  have hst : s.1 ≠ t := fun h ↦ htx (h ▸ hsx)
  have hrx' : r.1 ≠ x := fun h ↦ hx (h ▸ r.2)
  have hsx' : s.1 ≠ x := fun h ↦ hx (h ▸ s.2)
  have htx' : t ≠ x := fun h ↦ hx (h ▸ htK)
  exact hdiamond hrs' hrt hrx' hst hsx' htx'
    (hK.1 r.2 s.2 hrs') (hK.1 r.2 htK hrt)
    (hK.1 s.2 htK hst) hrx hsx htx

/-- With induced four-cycles also excluded, attachment sets belonging to
different maximal-clique vertices are anticomplete. -/
theorem maximalClique_attachments_anticomplete
    (G : SimpleGraph V) {K : Set V} (hK : Maximal G.IsClique K)
    (hdiamond : NoInducedDiamond G) (hfour : NoInducedFourCycle G) :
    ∀ {r s : K}, r ≠ s → ∀ {x y : V}, x ∉ K → y ∉ K →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y := by
  intro r s hrs x y hx hy hrx hsy hxy
  have hrs' : r.1 ≠ s.1 := fun h ↦ hrs (Subtype.ext h)
  have hsx : ¬ G.Adj s.1 x :=
    maximalClique_attachment_unique G hK hdiamond (r := s) (s := r) hrs.symm hx hrx
  have hry : ¬ G.Adj r.1 y :=
    maximalClique_attachment_unique G hK hdiamond (r := r) (s := s) hrs hy hsy
  have hrx' : r.1 ≠ x := fun h ↦ hx (h ▸ r.2)
  have hry' : r.1 ≠ y := fun h ↦ hy (h ▸ r.2)
  have hxy' : x ≠ y := hxy.ne
  have hxs : x ≠ s.1 := fun h ↦ hx (h ▸ s.2)
  have hys : y ≠ s.1 := fun h ↦ hy (h ▸ s.2)
  exact hfour hrx' hry' hrs' hxy' hxs hys
    hrx hxy hsy.symm (hK.1 s.2 r.2 hrs'.symm) hry (fun h ↦ hsx h.symm)

/-- A shortest-cycle hypothesis stated directly in terms of all cycle walks. -/
def IsShortestCycleLength (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∀ {v : V} (p : G.Walk v v), p.IsCycle → n ≤ p.length

end Erdos922Recolor
