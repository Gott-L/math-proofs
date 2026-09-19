/-
Copyright 2026. Released under the Apache 2.0 license.
Project initiation, direction and submission ownership: Gott-L.
Formal implementation: Codex assistance.

Independently formalizes the finite coloring argument in haipapa123's
JSP-000904 PR 586, commit daa68321eca18b869069e5cdec51ab5526d57558.
The source exposition is CC BY 4.0; mathematical attribution is retained.
-/
import E1087Core
import Mathlib.Data.Finset.Prod

open Finset

namespace Erdos1087

noncomputable def monochromaticPairs {β κ : Type*} [DecidableEq β]
    (E : Finset β) (c : β → κ) : Finset (Finset β) := by
  classical
  exact (E.powersetCard 2).filter (fun q => ∀ e ∈ q, ∀ f ∈ q, c e = c f)

@[simp] theorem mem_monochromaticPairs {β κ : Type*} [DecidableEq β]
    {E : Finset β} {c : β → κ} {q : Finset β} :
    q ∈ monochromaticPairs E c ↔
      q ∈ E.powersetCard 2 ∧ ∀ e ∈ q, ∀ f ∈ q, c e = c f := by
  classical
  simp [monochromaticPairs]

theorem monochromatic_pairs_le_ten {β κ : Type*} [DecidableEq β]
    (E : Finset β) (c : β → κ) (hE : E.card = 6)
    (hnot : ∃ a ∈ E, ∃ b ∈ E, c a ≠ c b) :
    (monochromaticPairs E c).card ≤ 10 := by
  classical
  obtain ⟨a, ha, b, hb, hab⟩ := hnot
  let A := E.filter (fun x => c x = c a)
  let B := E \ A
  let X := (A ×ˢ B).image (fun p => ({p.1, p.2} : Finset β))
  let M := monochromaticPairs E c
  have hAsub : A ⊆ E := filter_subset _ _
  have hBsub : B ⊆ E := sdiff_subset
  have hdis : Disjoint A B := disjoint_sdiff_self_right
  have haA : a ∈ A := by simp [A, ha]
  have hbB : b ∈ B := by simp [B, A, hb, Ne.symm hab]
  have hApos : 1 ≤ A.card := card_pos.mpr ⟨a, haA⟩
  have hBpos : 1 ≤ B.card := card_pos.mpr ⟨b, hbB⟩
  have hcards : A.card + B.card = 6 := by
    dsimp [B]
    simpa [hE, Nat.add_comm] using card_sdiff_add_card_eq_card hAsub
  have hne {x y : β} (hx : x ∈ A) (hy : y ∈ B) : x ≠ y := by
    intro h
    exact disjoint_left.mp hdis hx (h ▸ hy)
  have hXcard : X.card = A.card * B.card := by
    dsimp only [X]
    rw [card_image_of_injOn, card_product]
    intro p hp q hq heq
    change ({p.1, p.2} : Finset β) = {q.1, q.2} at heq
    obtain ⟨hpA, hpB⟩ := mem_product.mp hp
    obtain ⟨hqA, hqB⟩ := mem_product.mp hq
    have hpq : p.1 = q.1 := by
      have hmem : p.1 ∈ ({q.1, q.2} : Finset β) := by
        rw [← heq]
        simp
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with h | h
      · exact h
      · exact False.elim (hne hpA hqB h)
    have hpq' : p.2 = q.2 := by
      have hmem : p.2 ∈ ({q.1, q.2} : Finset β) := by
        rw [← heq]
        simp
      simp only [mem_insert, mem_singleton] at hmem
      rcases hmem with h | h
      · exact False.elim (hne hqA hpB h.symm)
      · exact h
    exact Prod.ext hpq hpq'
  have hXsub : X ⊆ E.powersetCard 2 := by
    intro q hq
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_image.mp hq
    obtain ⟨hx, hy⟩ := mem_product.mp hxy
    apply mem_powersetCard.mpr
    constructor
    · intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl
      · exact hAsub hx
      · exact hBsub hy
    · simp [hne hx hy]
  have hXM : Disjoint X M := by
    apply disjoint_left.mpr
    intro q hq hqM
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_image.mp hq
    obtain ⟨hx, hy⟩ := mem_product.mp hxy
    have hsame := (mem_monochromaticPairs.mp hqM).2 x (by simp) y (by simp)
    have hxcol : c x = c a := (mem_filter.mp hx).2
    have hyA : y ∈ A := mem_filter.mpr ⟨hBsub hy, hsame.symm.trans hxcol⟩
    exact disjoint_left.mp hdis hyA hy
  have hupper : X.card + M.card ≤ 15 := by
    rw [← card_union_of_disjoint hXM]
    calc
      (X ∪ M).card ≤ (E.powersetCard 2).card :=
        card_le_card (union_subset hXsub (fun _ h => (mem_monochromaticPairs.mp h).1))
      _ = 15 := by rw [card_powersetCard, hE]; decide
  rw [hXcard] at hupper
  have hcross : 5 ≤ A.card * B.card := by
    have hlow : 0 ≤ (A.card - 1) * (B.card - 1) := Nat.zero_le _
    have hA : A.card - 1 + 1 = A.card := Nat.sub_add_cancel hApos
    have hB : B.card - 1 + 1 = B.card := Nat.sub_add_cancel hBpos
    nlinarith
  change M.card ≤ 10
  omega

end Erdos1087
