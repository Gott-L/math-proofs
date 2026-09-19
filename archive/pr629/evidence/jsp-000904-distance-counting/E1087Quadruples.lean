/-
Copyright 2026. Released under the Apache 2.0 license.
Project initiation, direction and submission ownership: Gott-L.
Formal proof development and implementation: Codex assistance.

Independent formalization of the counting framework in haipapa123's
JSP-000904 research submission, commit daa68321eca18b869069e5cdec51ab5526d57558.
The source exposition is CC BY 4.0; see the accompanying attribution record.
-/
import E1087Core
import Mathlib.Data.Finset.Prod

open Finset
open Classical
open scoped BigOperators

namespace Erdos1087

variable {α κ : Type*} [DecidableEq α]

/-- All four entries are ordered; each of the two edges is nondegenerate. -/
noncomputable def orderedQuadruples (P : Finset α) (d : α → α → κ) :
    Finset ((α × α) × (α × α)) := by
  classical
  exact ((P ×ˢ P) ×ˢ (P ×ˢ P)).filter
    (fun q => q.1.1 ≠ q.1.2 ∧ q.2.1 ≠ q.2.2 ∧ d q.1.1 q.1.2 = d q.2.1 q.2.2)

/-- The two orientations of an unordered edge, expressed as a fiber. -/
def edgeOrientations (P e : Finset α) : Finset (α × α) :=
  (P ×ˢ P).filter (fun z => z.1 ≠ z.2 ∧ {z.1, z.2} = e)

noncomputable def selectedTwo (S : Finset α) (R : Finset α → Prop) := by
  classical
  exact (S.powersetCard 2).filter R

noncomputable def orderedDistinct (S : Finset α) (R : Finset α → Prop) := by
  classical
  exact (S ×ˢ S).filter (fun z => z.1 ≠ z.2 ∧ R {z.1, z.2})

def IsMonochromatic (c : α → κ) (q : Finset α) : Prop :=
  ∀ e ∈ q, ∀ f ∈ q, c e = c f

private theorem pair_eq_pair_cases {a b x y : α}
    (hxy : x ≠ y)
    (h : ({x, y} : Finset α) = {a, b}) :
    (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  have hx : x = a ∨ x = b := by
    have : x ∈ ({a, b} : Finset α) := h ▸ (by simp)
    simpa using this
  have hy : y = a ∨ y = b := by
    have : y ∈ ({a, b} : Finset α) := h ▸ (by simp)
    simpa using this
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact (hxy rfl).elim
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact (hxy rfl).elim

theorem edgeOrientations_pair {P : Finset α} {a b : α}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) :
    edgeOrientations P {a, b} = {(a, b), (b, a)} := by
  ext ⟨x, y⟩
  simp only [edgeOrientations, mem_filter, mem_product, mem_insert, mem_singleton]
  constructor
  · rintro ⟨_, hxy, heq⟩
    rcases pair_eq_pair_cases hxy heq with h | h
    · exact Or.inl (Prod.ext h.1 h.2)
    · exact Or.inr (Prod.ext h.1 h.2)
  · rintro (h | h)
    · cases h
      exact ⟨⟨ha, hb⟩, hab, rfl⟩
    · cases h
      exact ⟨⟨hb, ha⟩, hab.symm, by simp [pair_comm]⟩

theorem edgeOrientations_card {P e : Finset α} (he : e ∈ P.powersetCard 2) :
    (edgeOrientations P e).card = 2 := by
  obtain ⟨hesub, hecard⟩ := mem_powersetCard.mp he
  obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hecard
  rw [edgeOrientations_pair (hesub (by simp)) (hesub (by simp)) hab]
  exact card_pair (by intro h; exact hab (congrArg Prod.fst h) : (a, b) ≠ (b, a))

private theorem ordered_distinct_card (S : Finset α) (R : Finset α → Prop) :
    (orderedDistinct S R).card = 2 * (selectedTwo S R).card := by
  classical
  let U := orderedDistinct S R
  let T := selectedTwo S R
  have hmap : U.toSet.MapsTo (fun z => ({z.1, z.2} : Finset α)) T := by
    intro z hz
    obtain ⟨hzS, hzneq, hzR⟩ := mem_filter.mp hz
    apply mem_filter.mpr
    refine ⟨mem_powersetCard.mpr ⟨?_, card_pair hzneq⟩, hzR⟩
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · exact (mem_product.mp hzS).1
    · have haz : a = z.2 := mem_singleton.mp ha
      simpa [haz] using (mem_product.mp hzS).2
  have hfiber (e : Finset α) (he : e ∈ T) :
      (U.filter (fun z => ({z.1, z.2} : Finset α) = e)).card = 2 := by
    obtain ⟨heP, heR⟩ := mem_filter.mp he
    have heq : U.filter (fun z => ({z.1, z.2} : Finset α) = e) =
        edgeOrientations S e := by
      ext z
      simp only [U, orderedDistinct, edgeOrientations, mem_filter]
      constructor
      · rintro ⟨⟨hS, hne, _⟩, hpair⟩
        exact ⟨hS, hne, hpair⟩
      · rintro ⟨hS, hne, hpair⟩
        exact ⟨⟨hS, hne, hpair ▸ heR⟩, hpair⟩
    rw [heq]
    exact edgeOrientations_card heP
  calc
    U.card = ∑ e ∈ T, (U.filter (fun z => ({z.1, z.2} : Finset α) = e)).card :=
      card_eq_sum_card_fiberwise hmap
    _ = ∑ _e ∈ T, 2 := sum_congr rfl hfiber
    _ = 2 * T.card := by simp [Nat.mul_comm]

noncomputable def sameColorPairs (S : Finset α) (c : α → κ) : Finset (α × α) := by
  classical
  exact (S ×ˢ S).filter (fun z => c z.1 = c z.2)

private theorem pair_monochromatic_iff (c : α → κ) (a b : α) :
    IsMonochromatic c {a, b} ↔ c a = c b := by
  constructor
  · intro h
    exact h a (by simp) b (by simp)
  · intro h e he f hf
    simp only [mem_insert, mem_singleton] at he hf
    rcases he with rfl | rfl <;> rcases hf with rfl | rfl
    · rfl
    · exact h
    · exact h.symm
    · rfl

theorem sameColorPairs_card (S : Finset α) (c : α → κ) :
    (sameColorPairs S c).card = S.card +
      2 * (selectedTwo S (IsMonochromatic c)).card := by
  classical
  have hdiag : ((sameColorPairs S c).filter (fun z => z.1 = z.2)).card = S.card := by
    apply card_bij (fun z _ => z.1)
    · intro z hz
      exact (mem_product.mp (mem_filter.mp (mem_filter.mp hz).1).1).1
    · intro z hz w hw heq
      have hzdiag := (mem_filter.mp hz).2
      have hwdiag := (mem_filter.mp hw).2
      exact Prod.ext heq (hzdiag.symm.trans (heq.trans hwdiag))
    · intro a ha
      refine ⟨(a, a), ?_, rfl⟩
      simp [sameColorPairs, ha]
  have hoff : (sameColorPairs S c).filter (fun z => ¬ z.1 = z.2) =
      orderedDistinct S (IsMonochromatic c) := by
    ext z
    simp only [sameColorPairs, orderedDistinct, mem_filter, pair_monochromatic_iff]
    tauto
  rw [← filter_card_add_filter_neg_card_eq_card (p := fun z : α × α => z.1 = z.2),
    hdiag, hoff, ordered_distinct_card]

set_option maxHeartbeats 600000 in
/-- Forgetting both edge orientations has exactly four preimages. -/
theorem orderedQuadruples_card (P : Finset α) (d : α → α → κ)
    (c : Finset α → κ) (hc : ∀ a b, a ≠ b → c {a, b} = d a b) :
    (orderedQuadruples P d).card =
      4 * ((edges P).card + 2 * (equalPairs P c).card) := by
  classical
  let F : ((α × α) × (α × α)) → Finset α × Finset α :=
    fun q => ({q.1.1, q.1.2}, {q.2.1, q.2.2})
  let T := sameColorPairs (edges P) c
  have hmap : (orderedQuadruples P d).toSet.MapsTo F T := by
    intro q hq
    obtain ⟨hP, hne1, hne2, hd⟩ := mem_filter.mp hq
    obtain ⟨hP1, hP2⟩ := mem_product.mp hP
    obtain ⟨ha, hb⟩ := mem_product.mp hP1
    obtain ⟨hu, hv⟩ := mem_product.mp hP2
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact mem_edges.mpr
        ⟨insert_subset_iff.mpr ⟨ha, singleton_subset_iff.mpr hb⟩, card_pair hne1⟩
    · exact mem_edges.mpr
        ⟨insert_subset_iff.mpr ⟨hu, singleton_subset_iff.mpr hv⟩, card_pair hne2⟩
    · change c {q.1.1, q.1.2} = c {q.2.1, q.2.2}
      rw [hc _ _ hne1, hc _ _ hne2, hd]
  have hfiber (z : Finset α × Finset α) (hz : z ∈ T) :
      ((orderedQuadruples P d).filter (fun q => F q = z)).card = 4 := by
    obtain ⟨hE, hcolor⟩ := mem_filter.mp hz
    obtain ⟨he, hf⟩ := mem_product.mp hE
    have heq : (orderedQuadruples P d).filter (fun q => F q = z) =
        edgeOrientations P z.1 ×ˢ edgeOrientations P z.2 := by
      ext q
      simp only [orderedQuadruples, edgeOrientations, mem_filter, mem_product]
      constructor
      · rintro ⟨⟨⟨hP1, hP2⟩, hne1, hne2, _⟩, hF⟩
        exact ⟨⟨hP1, hne1, congrArg Prod.fst hF⟩,
          ⟨hP2, hne2, congrArg Prod.snd hF⟩⟩
      · rintro ⟨⟨hP1, hne1, heq⟩, ⟨hP2, hne2, hfq⟩⟩
        refine ⟨⟨⟨hP1, hP2⟩, hne1, hne2, ?_⟩, Prod.ext heq hfq⟩
        rw [← hc _ _ hne1, ← hc _ _ hne2, heq, hfq]
        exact hcolor
    rw [heq, card_product, edgeOrientations_card he, edgeOrientations_card hf]
  calc
    (orderedQuadruples P d).card =
        ∑ z ∈ T, ((orderedQuadruples P d).filter (fun q => F q = z)).card :=
      card_eq_sum_card_fiberwise hmap
    _ = ∑ _z ∈ T, 4 := sum_congr rfl hfiber
    _ = 4 * T.card := by simp [Nat.mul_comm]
    _ = 4 * ((edges P).card + 2 * (equalPairs P c).card) := by
      change 4 * (sameColorPairs (edges P) c).card = _
      rw [sameColorPairs_card (edges P) c]
      have hsel : selectedTwo (edges P) (IsMonochromatic c) = equalPairs P c := by
        ext q
        simp only [selectedTwo, equalPairs, IsMonochromatic, mem_filter]
      rw [hsel]

end Erdos1087

#print axioms Erdos1087.edgeOrientations_card
#print axioms Erdos1087.sameColorPairs_card
#print axioms Erdos1087.orderedQuadruples_card
