/-
Copyright 2026. Released under the Apache 2.0 license.
Project initiation, objectives and research direction: Gott-L.
Formal proof development, implementation and checks: Codex assistance.
Finite matching lemmas for the classical Erdős–Goodman–Pósa argument.
No claim of a new mathematical discovery is made.
-/
import EGPDefs
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option warningAsError true

namespace EGP
open Finset

variable {V : Type*} [DecidableEq V]

theorem matching_covered_subset {R : V → V → Prop} {N : Finset V}
    {M : Finset (Finset V)} (h : MatchingOn R N M) : covered M ⊆ N := by
  intro a ha
  obtain ⟨e, he, hae⟩ := mem_biUnion.mp ha
  exact (h.1 e he).2.1 hae

theorem matching_covered_card {R : V → V → Prop} {N : Finset V}
    {M : Finset (Finset V)} (h : MatchingOn R N M) :
    (covered M).card = 2 * M.card := by
  calc
    (covered M).card = ∑ e ∈ M, e.card := card_biUnion h.2
    _ = ∑ _e ∈ M, 2 := sum_congr rfl (fun e he => (h.1 e he).1)
    _ = 2 * M.card := by simp [Nat.mul_comm]

/-- A cardinality-maximizing finite matching leaves no edge between two
uncovered vertices. Symmetry supplies the two-element clique and
irreflexivity excludes a loop as the proposed additional edge. -/
theorem exists_maximal_matching (R : V → V → Prop) (N : Finset V)
    (hsymm : Symmetric R) (hirr : Irreflexive R) :
    ∃ M, MatchingOn R N M ∧ MaximalMatching R N M := by
  classical
  let C := ((N.powersetCard 2).powerset).filter (MatchingOn R N)
  have hempty : (∅ : Finset (Finset V)) ∈ C := by
    simp [C, MatchingOn]
  obtain ⟨M, hM, hmax⟩ := C.exists_max_image Finset.card ⟨∅, hempty⟩
  have hm : MatchingOn R N M := (mem_filter.mp hM).2
  refine ⟨M, hm, ?_⟩
  intro a ha b hb han hbn hab
  have hne : a ≠ b := by
    rintro rfl
    exact hirr a hab
  have hecard : ({a,b} : Finset V).card = 2 := by simp [hne]
  have hesub : ({a,b} : Finset V) ⊆ N := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact ha
    · exact mem_singleton.mp hx ▸ hb
  have heclique : Clique R ({a,b} : Finset V) := by
    intro x hx y hy hxy
    simp only [mem_insert, mem_singleton] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact (hxy rfl).elim
    · exact hab
    · exact hsymm hab
    · exact (hxy rfl).elim
  have hdis : ∀ f ∈ M, Disjoint ({a,b} : Finset V) f := by
    intro f hf
    apply disjoint_left.mpr
    intro x hx hxf
    have hcov : x ∈ covered M := mem_biUnion.mpr ⟨f, hf, hxf⟩
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact han hcov
    · exact hbn hcov
  have hnew : ({a,b} : Finset V) ∉ M := by
    intro he
    apply han
    exact mem_biUnion.mpr ⟨{a,b}, he, by simp⟩
  have hext : MatchingOn R N (insert {a,b} M) := by
    constructor
    · intro f hf
      rcases mem_insert.mp hf with rfl | hf
      · exact ⟨hecard, hesub, heclique⟩
      · exact hm.1 f hf
    · intro f hf g hg hfg
      rcases mem_insert.mp hf with rfl | hf
      · rcases mem_insert.mp hg with rfl | hg
        · exact (hfg rfl).elim
        · exact hdis g hg
      · rcases mem_insert.mp hg with rfl | hg
        · exact (hdis f hf).symm
        · exact hm.2 hf hg hfg
  have hextC : insert ({a,b} : Finset V) M ∈ C := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr ?_, hext⟩
    intro f hf
    exact mem_powersetCard.mpr ⟨(hext.1 f hf).2.1, (hext.1 f hf).1⟩
  have hle := hmax (insert ({a,b} : Finset V) M) hextC
  rw [card_insert_of_not_mem hnew] at hle
  omega

end EGP
