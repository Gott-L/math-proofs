/-
Local Lean 4.19 compatibility port, under Gott-L's direction with Codex assistance.
Original mathematics: Jon Folkman; original formal authors: Codex and GPT-5.6 Sol.
Copied/adapted from plby/lean-proofs at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos922.lean, SHA256
0bc22004ecbe76ab3cc3f263c29c76994b39017828ea835d987139fa324b9971.
This split preserves the original mathematical statements and proof attribution.
The public header is retained below. Local adaptations do not assert priority.
-/
/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 922.
https://www.erdosproblems.com/forum/thread/922

Informal authors:
- Jon Folkman

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos922.md
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Data.Set.Card
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

/-!
# Erdős Problem 922

This file formalizes Folkman's hereditary independence-number bound and
deduces the affirmative answer to Erdős Problem 922.  A detailed mathematical
proof and Leanization guide are in `tex/922.tex`.
-/

open SimpleGraph
open scoped ENat

namespace Erdos922

universe u

/-- The hypothesis in Problem 922, stated literally for every (not
necessarily induced or spanning) subgraph.  The inequality is the integral
form of `|I| ≥ (|V(H)| - k) / 2`. -/
def HasLargeIndependentSets {V : Type u} [Finite V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ H : G.Subgraph, ∃ I : Finset H.verts,
    H.coe.IsIndepSet I ∧ H.verts.ncard ≤ 2 * I.card + k

/-- The equivalent formulation on finite induced vertex sets. -/
def HasLargeIndependentSetsOnFinsets {V : Type u}
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, ∃ I : Finset V,
    I ⊆ S ∧ G.IsIndepSet I ∧ S.card ≤ 2 * I.card + k

/-- The literal subgraph hypothesis supplies an independent set in every
finite induced vertex set. -/
theorem HasLargeIndependentSets.onFinsets {V : Type u} [Finite V]
    {G : SimpleGraph V} {k : ℕ} (h : HasLargeIndependentSets G k) :
    HasLargeIndependentSetsOnFinsets G k := by
  classical
  intro S
  let H : G.Subgraph := (⊤ : G.Subgraph).induce (↑S : Set V)
  obtain ⟨J, hJ, hcard⟩ := h H
  let I : Finset V := J.map ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨I, ?_, ?_, ?_⟩
  · intro v hv
    simp only [I, Finset.mem_map, Function.Embedding.coeFn_mk] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact w.property
  · have himage : G.IsIndepSet (Subtype.val '' (↑J : Set H.verts)) := by
      exact (SimpleGraph.isIndepSet_induce (G := G)).mp hJ
    simpa only [I, Finset.coe_map, Function.Embedding.coeFn_mk] using himage
  · simpa only [H, SimpleGraph.Subgraph.induce_verts, Set.ncard_coe_Finset,
      I, Finset.card_map] using hcard

/-- The induced-finset formulation also implies the literal hypothesis for
arbitrary edge-deleted subgraphs. -/
theorem hasLargeIndependentSets_iff_onFinsets {V : Type u} [Finite V]
    {G : SimpleGraph V} {k : ℕ} :
    HasLargeIndependentSets G k ↔ HasLargeIndependentSetsOnFinsets G k := by
  classical
  refine ⟨HasLargeIndependentSets.onFinsets, ?_⟩
  intro h H
  letI : Fintype H.verts := Fintype.ofFinite H.verts
  let S : Finset V := H.verts.toFinset
  obtain ⟨I, hIS, hI, hcard⟩ := h S
  let J : Finset H.verts := I.subtype (fun v ↦ v ∈ H.verts)
  refine ⟨J, ?_, ?_⟩
  · rw [SimpleGraph.isIndepSet_iff]
    intro a ha b hb hab
    have haI : a.1 ∈ I := by
      change a ∈ J at ha
      simpa only [J, Finset.mem_subtype] using ha
    have hbI : b.1 ∈ I := by
      change b ∈ J at hb
      simpa only [J, Finset.mem_subtype] using hb
    exact fun hAdj ↦ hI haI hbI (Subtype.coe_ne_coe.mpr hab)
      (H.coe_adj_sub a b hAdj)
  · have hIfilter : I.filter (fun v ↦ v ∈ H.verts) = I := by
      exact Finset.filter_eq_self.mpr fun v hv ↦ by
        have : v ∈ S := hIS hv
        simpa only [S, Set.mem_toFinset] using this
    have hJcard : J.card = I.card := by
      simp only [J, Finset.card_subtype, hIfilter]
    rw [Set.ncard_eq_toFinset_card']
    simpa only [S, hJcard] using hcard

/-- The independence number restricted to the finite vertex set `S`. -/
noncomputable def alphaOn {V : Type u} (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun n ↦ ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet I ∧ I.card = n) S.card

/-- A largest independent subset witnessing `alphaOn`. -/
theorem exists_maximum_independent_subset {V : Type u}
    (G : SimpleGraph V) (S : Finset V) :
    ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet I ∧ I.card = alphaOn G S := by
  classical
  unfold alphaOn
  apply Nat.findGreatest_spec
    (P := fun n ↦ ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet I ∧ I.card = n)
    (m := 0) (Nat.zero_le _)
  exact ⟨∅, by simp⟩

theorem alphaOn_le_card {V : Type u} (G : SimpleGraph V) (S : Finset V) :
    alphaOn G S ≤ S.card := by
  classical
  unfold alphaOn
  exact Nat.findGreatest_le _

/-- Every independent subset has cardinality at most `alphaOn`. -/
theorem card_le_alphaOn {V : Type u} {G : SimpleGraph V}
    {I S : Finset V} (hIS : I ⊆ S) (hI : G.IsIndepSet I) :
    I.card ≤ alphaOn G S := by
  classical
  unfold alphaOn
  exact Nat.le_findGreatest (Finset.card_le_card hIS) ⟨I, hIS, hI, rfl⟩

@[simp] theorem alphaOn_empty {V : Type u} (G : SimpleGraph V) :
    alphaOn G ∅ = 0 := by
  exact Nat.le_zero.mp (alphaOn_le_card G ∅)

/-- Restricting the ambient finite vertex set cannot increase its independence
number. -/
theorem alphaOn_mono {V : Type u} {G : SimpleGraph V} {S T : Finset V}
    (hST : S ⊆ T) : alphaOn G S ≤ alphaOn G T := by
  obtain ⟨I, hIS, hI, hIa⟩ := exists_maximum_independent_subset G S
  rw [← hIa]
  exact card_le_alphaOn (hIS.trans hST) hI

/-- Restricting an independent set to a smaller finite set preserves
independence. -/
theorem indepSet_inter {V : Type u} {G : SimpleGraph V}
    {I S : Finset V} (hI : G.IsIndepSet I) : G.IsIndepSet (I ∩ S) := by
  classical
  exact hI.mono (by simp)

/-- Removing vertices outside `T` loses at most that many vertices from an
independent set. -/
theorem alphaOn_le_alphaOn_add_card_sdiff {V : Type u} [DecidableEq V]
    {G : SimpleGraph V}
    (S T : Finset V) :
    alphaOn G S ≤ alphaOn G (S ∩ T) + (S \ T).card := by
  classical
  obtain ⟨I, hIS, hI, hIa⟩ := exists_maximum_independent_subset G S
  have hinter : I ∩ T ⊆ S ∩ T := by
    intro v hv
    simp only [Finset.mem_inter] at hv ⊢
    exact ⟨hIS hv.1, hv.2⟩
  have hdiff : I \ T ⊆ S \ T := by
    intro v hv
    simp only [Finset.mem_sdiff] at hv ⊢
    exact ⟨hIS hv.1, hv.2⟩
  rw [← hIa, ← Finset.card_inter_add_card_sdiff I T]
  exact Nat.add_le_add (card_le_alphaOn hinter (hI.mono (by simp)))
    (Finset.card_le_card hdiff)

/-- Signed deficiency `|S| - 2 α(G[S])`. -/
noncomputable def potential {V : Type u} (G : SimpleGraph V) (S : Finset V) : ℤ :=
  (S.card : ℤ) - 2 * (alphaOn G S : ℤ)

@[simp] theorem potential_empty {V : Type u} (G : SimpleGraph V) :
    potential G ∅ = 0 := by simp [potential]

/-- The maximum signed deficiency of an induced finite vertex set. -/
noncomputable def f {V : Type u} [Fintype V] (G : SimpleGraph V) : ℤ := by
  classical
  exact ((Finset.univ : Finset V).powerset.image (potential G)).max' (by simp)

/-- A vertex set attaining the maximum deficiency. -/
theorem exists_maximum_potential {V : Type u} [Fintype V] (G : SimpleGraph V) :
    ∃ S : Finset V, potential G S = f G := by
  classical
  let P : Finset ℤ := (Finset.univ : Finset V).powerset.image (potential G)
  have hP : P.Nonempty := by simp [P]
  have hm : P.max' hP ∈ P := P.max'_mem hP
  obtain ⟨S, hS, hpot⟩ := Finset.mem_image.mp hm
  refine ⟨S, ?_⟩
  have hfuniv : S ⊆ (Finset.univ : Finset V) := Finset.subset_univ S
  have hmax : f G = P.max' hP := by
    simp only [f, P]
  exact hpot.trans hmax.symm

/-- Every potential is bounded by the maximum deficiency. -/
theorem potential_le_f {V : Type u} [Fintype V] (G : SimpleGraph V)
    (S : Finset V) : potential G S ≤ f G := by
  classical
  let P : Finset ℤ := (Finset.univ : Finset V).powerset.image (potential G)
  have hmem : potential G S ∈ P := by simp [P]
  have hle : potential G S ≤ P.max' ⟨potential G S, hmem⟩ := P.le_max' _ hmem
  simpa only [f, P] using hle

/-- The maximum deficiency is nonnegative because the empty vertex set has
potential zero. -/
theorem f_nonneg {V : Type u} [Fintype V] (G : SimpleGraph V) :
    0 ≤ f G := by
  simpa only [potential_empty] using potential_le_f G (∅ : Finset V)

/-- Bounding the maximum potential is exactly the same as bounding every
finite induced-set deficiency. -/
theorem f_le_iff_forall_potential_le {V : Type u} [Fintype V]
    (G : SimpleGraph V) (z : ℤ) :
    f G ≤ z ↔ ∀ S : Finset V, potential G S ≤ z := by
  constructor
  · intro hf S
    exact (potential_le_f G S).trans hf
  · intro h
    obtain ⟨S, hS⟩ := exists_maximum_potential G
    rw [← hS]
    exact h S

/-- Natural-cardinality form of `f ≤ k`.  This is the endpoint assumption
that is typically fed into Folkman's coloring bound. -/
theorem f_le_natCast_iff_forall_card_le {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) :
    f G ≤ (k : ℤ) ↔
      ∀ S : Finset V, S.card ≤ 2 * alphaOn G S + k := by
  rw [f_le_iff_forall_potential_le]
  constructor
  · intro h S
    have hS := h S
    rw [potential] at hS
    omega
  · intro h S
    have hS := h S
    rw [potential]
    omega

/-- An integral upper bound on the nonnegative maximum deficiency converts
to the corresponding natural-number upper bound. -/
theorem f_toNat_le_of_le_natCast {V : Type u} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (hf : f G ≤ (k : ℤ)) :
    (f G).toNat ≤ k := by
  have hnonneg := f_nonneg G
  omega

/-- Endpoint composition: once the general Folkman bound is known in terms
of the maximum signed deficiency, `f ≤ k` gives the requested `k + 2`
chromatic bound. -/
theorem chromaticNumber_le_add_two_of_f_le {V : Type u} [Fintype V]
    {G : SimpleGraph V} {k : ℕ}
    (hfolkman : G.chromaticNumber ≤ ((f G).toNat + 2 : ℕ∞))
    (hf : f G ≤ (k : ℤ)) :
    G.chromaticNumber ≤ (k + 2 : ℕ∞) := by
  refine hfolkman.trans ?_
  exact_mod_cast Nat.add_le_add_right (f_toNat_le_of_le_natCast hf) 2

/-- The subgraph hypothesis bounds every signed potential by `k`. -/
theorem potential_le_of_hasLargeIndependentSets {V : Type u} [Finite V]
    {G : SimpleGraph V} {k : ℕ} (h : HasLargeIndependentSets G k)
    (S : Finset V) : potential G S ≤ (k : ℤ) := by
  obtain ⟨I, hIS, hI, hcard⟩ := h.onFinsets S
  have hIa : I.card ≤ alphaOn G S := card_le_alphaOn hIS hI
  rw [potential]
  omega

/-- Consequently the maximum potential is bounded by `k`. -/
theorem f_le_of_hasLargeIndependentSets {V : Type u} [Fintype V]
    {G : SimpleGraph V} {k : ℕ} (h : HasLargeIndependentSets G k) :
    f G ≤ (k : ℤ) := by
  obtain ⟨S, hS⟩ := exists_maximum_potential G
  rw [← hS]
  exact potential_le_of_hasLargeIndependentSets h S

end Erdos922

namespace SimpleGraph

section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Hajnal's union--intersection inequality for a nonempty finite family of
maximum independent sets. -/
theorem hajnal_maximumIndepSet_family
    (G : SimpleGraph V) (F : Finset (Finset V)) (hF : F.Nonempty)
    (hmax : ∀ I ∈ F, G.IsMaximumIndepSet I) :
    2 * G.indepNum ≤ (F.inf id).card + (F.sup id).card := by
  classical
  induction F using Finset.induction with
  | empty => simp at hF
  | @insert I F hIF ih =>
      by_cases hFe : F = ∅
      · subst F
        have hI : G.IsMaximumIndepSet I := hmax I (by simp)
        have hIc := G.maximumIndepSet_card_eq_indepNum I hI
        simp only [Finset.inf_insert, Finset.inf_empty, Finset.sup_insert, Finset.sup_empty,
          inf_top_eq, sup_bot_eq]
        change 2 * G.indepNum ≤ I.card + I.card
        omega
      · have hFn : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFe
        have hI : G.IsMaximumIndepSet I := hmax I (by simp)
        have hmaxF : ∀ J ∈ F, G.IsMaximumIndepSet J := by
          intro J hJ
          exact hmax J (Finset.mem_insert_of_mem hJ)
        have hIH := ih hFn hmaxF
        let C : Finset V := F.inf id
        let U : Finset V := F.sup id
        by_cases hcard : (C \ I).card ≤ (I \ U).card
        · have hC := Finset.card_sdiff_add_card_inter C I
          have hU := Finset.card_sdiff_add_card I U
          simp only [Finset.inf_insert, Finset.sup_insert]
          change 2 * G.indepNum ≤ (I ∩ C).card + (I ∪ U).card
          change 2 * G.indepNum ≤ C.card + U.card at hIH
          rw [Finset.inter_comm I C]
          omega
        · exfalso
          have hcard' : (I \ U).card < (C \ I).card := Nat.lt_of_not_ge hcard
          have hmemC : ∀ {x : V}, x ∈ C ↔ ∀ J ∈ F, x ∈ J := by
            intro x
            change x ∈ F.inf id ↔ _
            rw [← Finset.inf'_eq_inf hFn]
            simp
          have hmemU : ∀ {x : V}, x ∈ U ↔ ∃ J ∈ F, x ∈ J := by
            intro x
            change x ∈ F.sup id ↔ _
            simp
          let J : Finset V := (I ∩ U) ∪ (C \ I)
          have hJ : G.IsIndepSet J := by
            intro x hx y hy hxy
            change x ∈ J at hx
            change y ∈ J at hy
            simp only [J, Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hx hy
            rcases hx with hx | hx <;> rcases hy with hy | hy
            · exact hI.isIndepSet hx.1 hy.1 hxy
            · obtain ⟨K, hKF, hxK⟩ := hmemU.mp hx.2
              exact (hmaxF K hKF).isIndepSet hxK (hmemC.mp hy.1 K hKF) hxy
            · obtain ⟨K, hKF, hyK⟩ := hmemU.mp hy.2
              exact (hmaxF K hKF).isIndepSet (hmemC.mp hx.1 K hKF) hyK hxy
            · obtain ⟨K, hKF⟩ := hFn
              exact (hmaxF K hKF).isIndepSet (hmemC.mp hx.1 K hKF)
                (hmemC.mp hy.1 K hKF) hxy
          have hdisj : Disjoint (I ∩ U) (C \ I) := by
            rw [Finset.disjoint_left]
            intro x hxI hxC
            change x ∈ I ∩ U at hxI
            change x ∈ C \ I at hxC
            simp only [Finset.mem_inter] at hxI
            simp only [Finset.mem_sdiff] at hxC
            exact hxC.2 hxI.1
          have hJcard : J.card = (I ∩ U).card + (C \ I).card := by
            exact Finset.card_union_of_disjoint hdisj
          have hIcard := Finset.card_inter_add_card_sdiff I U
          have hle := hI.maximum J hJ
          omega

end

variable {V : Type*} [Fintype V]

/-- If the independence number is more than half the vertex count, one vertex
lies in every maximum independent set. -/
theorem exists_mem_all_maximumIndepSet_of_card_lt_two_mul_indepNum
    (G : SimpleGraph V) (hlarge : Fintype.card V < 2 * G.indepNum) :
    ∃ v : V, ∀ I : Finset V, G.IsMaximumIndepSet I → v ∈ I := by
  classical
  let F : Finset (Finset V) := (Finset.univ : Finset (Finset V)).filter G.IsMaximumIndepSet
  have hF : F.Nonempty := by
    obtain ⟨I, hI⟩ := G.maximumIndepSet_exists
    exact ⟨I, by simp [F, hI]⟩
  have hmax : ∀ I ∈ F, G.IsMaximumIndepSet I := by
    intro I hI
    simpa [F] using hI
  have hH := hajnal_maximumIndepSet_family G F hF hmax
  have hU : (F.sup id).card ≤ Fintype.card V := (F.sup id).card_le_univ
  have hinter : (F.inf id).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he] at hH
    simp only [Finset.card_empty, zero_add] at hH
    omega
  obtain ⟨v, hv⟩ := hinter
  refine ⟨v, ?_⟩
  intro I hI
  have hIF : I ∈ F := by simp [F, hI]
  rw [← Finset.inf'_eq_inf hF] at hv
  exact (Finset.mem_inf' hF).mp hv I hIF

end SimpleGraph
