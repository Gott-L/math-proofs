/-
Copyright 2026. Released under the Apache 2.0 license.
Project initiation, direction and submission ownership: Gott-L.
Formal proof development and implementation: Codex assistance.

An independent formalization of the counting framework in haipapa123's
JSP-000904 research submission, commit daa68321eca18b869069e5cdec51ab5526d57558.
The source exposition is CC BY 4.0; see the accompanying attribution record.
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset

namespace Erdos1087

variable {α κ : Type*} [DecidableEq α]

def edges (P : Finset α) : Finset (Finset α) := P.powersetCard 2

noncomputable def equalPairs (P : Finset α) (c : Finset α → κ) :
    Finset (Finset (Finset α)) := by
  classical
  exact ((edges P).powersetCard 2).filter
    (fun q => ∀ e ∈ q, ∀ f ∈ q, c e = c f)

def support (q : Finset (Finset α)) : Finset α := q.biUnion id

noncomputable def trianglePairs (P : Finset α) (c : Finset α → κ) :=
  (equalPairs P c).filter (fun q => (support q).card = 3)

noncomputable def disjointPairs (P : Finset α) (c : Finset α → κ) :=
  (equalPairs P c).filter (fun q => (support q).card = 4)

noncomputable def weight (S : Finset α) (c : Finset α → κ) : ℕ :=
  (equalPairs S c).card

noncomputable def totalWeight (P : Finset α) (c : Finset α → κ) : ℕ :=
  ∑ S ∈ P.powersetCard 4, weight S c

noncomputable def badFourSets (P : Finset α) (c : Finset α → κ) :=
  (P.powersetCard 4).filter (fun S => 0 < weight S c)

noncomputable def badCount (P : Finset α) (c : Finset α → κ) : ℕ :=
  (badFourSets P c).card

omit [DecidableEq α] in
@[simp] theorem mem_edges {P e : Finset α} :
    e ∈ edges P ↔ e ⊆ P ∧ e.card = 2 := mem_powersetCard

omit [DecidableEq α] in
theorem mem_equalPairs {P : Finset α} {c : Finset α → κ}
    {q : Finset (Finset α)} : q ∈ equalPairs P c ↔
    q ⊆ edges P ∧ q.card = 2 ∧ ∀ e ∈ q, ∀ f ∈ q, c e = c f := by
  classical
  simp [equalPairs, and_assoc]

@[simp] theorem support_pair (e f : Finset α) : support {e, f} = e ∪ f := by
  simp [support]

theorem support_subset {P : Finset α} {c : Finset α → κ}
    {q : Finset (Finset α)} (hq : q ∈ equalPairs P c) : support q ⊆ P := by
  intro x hx
  obtain ⟨e, he, hx⟩ := mem_biUnion.mp hx
  exact (mem_edges.mp ((mem_equalPairs.mp hq).1 he)).1 hx

theorem support_card {P : Finset α} {c : Finset α → κ}
    {q : Finset (Finset α)} (hq : q ∈ equalPairs P c) :
    (support q).card = 3 ∨ (support q).card = 4 := by
  obtain ⟨hqsub, hqcard, _⟩ := mem_equalPairs.mp hq
  obtain ⟨e, f, hef, rfl⟩ := card_eq_two.mp hqcard
  have he := (mem_edges.mp (hqsub (by simp : e ∈ ({e, f} : Finset _)))).2
  have hf := (mem_edges.mp (hqsub (by simp : f ∈ ({e, f} : Finset _)))).2
  rw [support_pair]
  have hupper := card_union_le e f
  have hlower := card_le_card (subset_union_left : e ⊆ e ∪ f)
  have hne : (e ∪ f).card ≠ 2 := by
    intro h
    have heq : e = e ∪ f := eq_of_subset_of_card_le subset_union_left (by omega)
    have hfq : f = e ∪ f := eq_of_subset_of_card_le subset_union_right (by omega)
    exact hef (heq.trans hfq.symm)
  omega

theorem equalPairs_card_partition (P : Finset α) (c : Finset α → κ) :
    (equalPairs P c).card = (trianglePairs P c).card + (disjointPairs P c).card := by
  classical
  have h : (equalPairs P c).filter (fun q => ¬ (support q).card = 3) =
      disjointPairs P c := by
    ext q
    simp only [mem_filter, disjointPairs]
    constructor
    · intro hq
      exact ⟨hq.1, (support_card hq.1).resolve_left hq.2⟩
    · intro hq
      exact ⟨hq.1, by omega⟩
  rw [← filter_card_add_filter_neg_card_eq_card (p := fun q => (support q).card = 3), h]
  rfl

end Erdos1087
