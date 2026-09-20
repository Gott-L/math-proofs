import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Sum
import Mathlib.Tactic.Linarith

/-!
An elementary join lower bound for clique extremal numbers.
The proof uses a finite maximizer, not Turán's theorem or its formula.
-/

open Finset Fintype
open scoped BigOperators

namespace GottL897

variable {V W : Type*}

/-- On complete graphs, non-induced copies and induced embeddings coincide. -/
theorem cliqueFree_iff_top_free (G : SimpleGraph V) (r : ℕ) :
    G.CliqueFree r ↔ (⊤ : SimpleGraph (Fin r)).Free G := by
  classical
  constructor
  · intro h ⟨f⟩
    let e : (⊤ : SimpleGraph (Fin r)) ↪g G :=
      { f.toEmbedding with
        map_rel_iff' := by
          intro i j
          constructor
          · intro hij
            exact (SimpleGraph.top_adj i j).mpr (fun he => by
              subst j
              exact G.loopless (f i) hij)
          · exact f.toHom.map_rel' }
    exact G.not_cliqueFree_of_top_embedding e h
  · intro h
    by_contra hc
    exact h ⟨(G.topEmbeddingOfNotCliqueFree hc).toCopy⟩

/-- Add an independent vertex set and every edge crossing to it. -/
def independentJoin (H : SimpleGraph V) : SimpleGraph (V ⊕ W) where
  Adj
    | .inl x, .inl y => H.Adj x y
    | .inr _, .inr _ => False
    | .inl _, .inr _ => True
    | .inr _, .inl _ => True
  symm := by
    intro x y h
    cases x <;> cases y
    · exact H.symm h
    · trivial
    · trivial
    · exact h
  loopless := by
    intro x
    cases x
    · exact H.loopless _
    · exact id

instance (H : SimpleGraph V) [DecidableRel H.Adj] :
    DecidableRel (independentJoin (W := W) H).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [independentJoin] <;> infer_instance

theorem independentJoin_cliqueFree {H : SimpleGraph V} {r : ℕ}
    (hH : H.CliqueFree (r - 1)) :
    (independentJoin (W := W) H).CliqueFree r := by
  classical
  intro s hs
  have hright : s.toRight.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro x hx y hy
    by_contra hxy
    have := hs.isClique (Finset.mem_toRight.mp hx) (Finset.mem_toRight.mp hy)
      (by simpa using hxy)
    exact this
  have hleft : H.IsClique (s.toLeft : Set V) := by
    intro x hx y hy hxy
    exact hs.isClique (Finset.mem_toLeft.mp hx) (Finset.mem_toLeft.mp hy)
      (by simpa using hxy)
  have hcard := Finset.card_toLeft_add_card_toRight (u := s)
  have hsCard := hs.card_eq
  have hle : r - 1 ≤ s.toLeft.card := by omega
  obtain ⟨t, hts, ht⟩ := Finset.exists_subset_card_eq hle
  exact hH t ⟨hleft.subset hts, ht⟩

open Classical in
theorem independentJoin_degree_left [Fintype V] [Fintype W]
    (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) :
    (independentJoin (W := W) H).degree (.inl v) = H.degree v + Fintype.card W := by
  have hn : (independentJoin (W := W) H).neighborFinset (.inl v) =
      (H.neighborFinset v).disjSum (Finset.univ : Finset W) := by
    ext x
    cases x <;> simp [SimpleGraph.mem_neighborFinset, independentJoin]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn, Finset.card_disjSum]
  simp

open Classical in
theorem independentJoin_degree_right [Fintype V] [Fintype W]
    (H : SimpleGraph V) [DecidableRel H.Adj] (w : W) :
    (independentJoin (W := W) H).degree (.inr w) = Fintype.card V := by
  have hn : (independentJoin (W := W) H).neighborFinset (.inr w) =
      (Finset.univ : Finset V).disjSum (∅ : Finset W) := by
    ext x
    cases x <;> simp [SimpleGraph.mem_neighborFinset, independentJoin]
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hn, Finset.card_disjSum]
  simp

open Classical in
theorem independentJoin_card_edges [Fintype V] [Fintype W]
    (H : SimpleGraph V) [DecidableRel H.Adj] :
    (independentJoin (W := W) H).edgeFinset.card =
      H.edgeFinset.card + Fintype.card V * Fintype.card W := by
  have hsum := (independentJoin (W := W) H).sum_degrees_eq_twice_card_edges
  rw [Fintype.sum_sum_type] at hsum
  simp only [independentJoin_degree_left, independentJoin_degree_right,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul] at hsum
  rw [H.sum_degrees_eq_twice_card_edges] at hsum
  nlinarith

/-- Join a maximum `(r-1)`-clique-free graph to an independent set.
This lower bound needs no evaluation of either extremal number. -/
theorem clique_extremal_join_le {n d r : ℕ} (hr : 3 ≤ r) (hd : d ≤ n) :
    SimpleGraph.extremalNumber d (⊤ : SimpleGraph (Fin (r - 1))) + d * (n - d) ≤
      SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) := by
  classical
  have hex : ∃ H : SimpleGraph (Fin d),
      (⊤ : SimpleGraph (Fin (r - 1))).Free H := by
    refine ⟨⊥, (cliqueFree_iff_top_free _ _).mp ?_⟩
    exact SimpleGraph.cliqueFree_bot (by omega)
  obtain ⟨H, inst, hH⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists
      ((⊤ : SimpleGraph (Fin (r - 1))).Free)).mpr hex
  letI := inst
  have hfree : (⊤ : SimpleGraph (Fin r)).Free
      (independentJoin (W := Fin (n - d)) H) :=
    (cliqueFree_iff_top_free _ _).mp
      (independentJoin_cliqueFree ((cliqueFree_iff_top_free _ _).mpr hH.prop))
  have hb := SimpleGraph.card_edgeFinset_le_extremalNumber hfree
  rw [independentJoin_card_edges] at hb
  have he := SimpleGraph.card_edgeFinset_of_isExtremal_free hH
  simp only [Fintype.card_fin] at he
  rw [he] at hb
  simpa only [Fintype.card_sum, Fintype.card_fin, Nat.add_sub_of_le hd] using hb

end GottL897
