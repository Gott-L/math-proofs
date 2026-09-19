/-
Copyright 2026. Released under the Apache 2.0 license.
Independent Lean implementation with Codex assistance for Gott-L's project.
The double-counting argument follows haipapa123's JSP-000904 note,
commit daa68321eca18b869069e5cdec51ab5526d57558 (CC BY 4.0).
-/
import E1087Core
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset

namespace Erdos1087

variable {α κ : Type*} [DecidableEq α]

theorem support_subset_iff {q : Finset (Finset α)} {S : Finset α} :
    support q ⊆ S ↔ ∀ e ∈ q, e ⊆ S := by
  simp [support, biUnion_subset]

theorem equalPairs_restrict {P S : Finset α} (hSP : S ⊆ P)
    (c : Finset α → κ) :
    equalPairs S c = (equalPairs P c).filter (fun q => support q ⊆ S) := by
  classical
  ext q
  rw [mem_filter, mem_equalPairs, mem_equalPairs, support_subset_iff]
  constructor
  · intro h
    refine ⟨⟨?_, h.2⟩, ?_⟩
    · intro e he
      exact mem_edges.mpr ⟨((mem_edges.mp (h.1 he)).1).trans hSP,
        (mem_edges.mp (h.1 he)).2⟩
    · intro e he
      exact (mem_edges.mp (h.1 he)).1
  · rintro ⟨h, hsub⟩
    refine ⟨?_, h.2⟩
    intro e he
    exact mem_edges.mpr ⟨hsub e he, (mem_edges.mp (h.1 he)).2⟩

theorem card_four_supersets_three {P U : Finset α}
    (hUP : U ⊆ P) (hU : U.card = 3) :
    ((P.powersetCard 4).filter (fun S => U ⊆ S)).card = P.card - 3 := by
  classical
  have heq : (P.powersetCard 4).filter (fun S => U ⊆ S) =
      (P \ U).image (fun x => insert x U) := by
    ext S
    simp only [mem_filter, mem_powersetCard, mem_image]
    constructor
    · rintro ⟨⟨hSP, hS⟩, hUS⟩
      have hdiff : (S \ U).card = 1 := by rw [card_sdiff hUS, hS, hU]
      obtain ⟨x, hx⟩ := card_eq_one.mp hdiff
      have hxmem : x ∈ S \ U := by rw [hx]; simp
      have hxin := mem_sdiff.mp hxmem
      refine ⟨x, mem_sdiff.mpr ⟨hSP hxin.1, hxin.2⟩, ?_⟩
      exact eq_of_subset_of_card_le (insert_subset hxin.1 hUS)
        (by rw [card_insert_of_not_mem hxin.2, hU, hS])
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hxP, hxU⟩ := mem_sdiff.mp hx
      exact ⟨⟨insert_subset hxP hUP, by rw [card_insert_of_not_mem hxU, hU]⟩,
        subset_insert _ _⟩
  rw [heq, card_image_of_injOn, card_sdiff hUP, hU]
  intro x hx y hy hxy
  change insert x U = insert y U at hxy
  have h : x ∈ insert y U := by rw [← hxy]; exact mem_insert_self _ _
  exact (mem_insert.mp h).resolve_right (mem_sdiff.mp hx).2

theorem card_four_supersets_four {P U : Finset α}
    (hUP : U ⊆ P) (hU : U.card = 4) :
    ((P.powersetCard 4).filter (fun S => U ⊆ S)).card = 1 := by
  classical
  have heq : (P.powersetCard 4).filter (fun S => U ⊆ S) = {U} := by
    ext S
    simp only [mem_filter, mem_powersetCard, mem_singleton]
    constructor
    · rintro ⟨⟨_, hS⟩, hUS⟩
      exact (eq_of_subset_of_card_le hUS (by omega)).symm
    · rintro rfl
      exact ⟨⟨hUP, hU⟩, subset_refl _⟩
  rw [heq, card_singleton]

/-- Each equal-edge pair occurs in as many four-sets as contain its support. -/
theorem totalWeight_as_support_sum (P : Finset α) (c : Finset α → κ) :
    totalWeight P c = ∑ q ∈ equalPairs P c,
      ((P.powersetCard 4).filter (fun S => support q ⊆ S)).card := by
  classical
  calc
    totalWeight P c = ∑ S ∈ P.powersetCard 4,
        ∑ q ∈ equalPairs P c, if support q ⊆ S then 1 else 0 := by
      unfold totalWeight
      apply sum_congr rfl
      intro S hS
      rw [weight, equalPairs_restrict (mem_powersetCard.mp hS).1,
        card_eq_sum_ones, sum_filter]
    _ = ∑ q ∈ equalPairs P c,
        ∑ S ∈ P.powersetCard 4, if support q ⊆ S then 1 else 0 := sum_comm
    _ = _ := by simp only [card_eq_sum_ones, sum_filter]

/-- The exact decomposition by supports of size three and four. -/
theorem totalWeight_identity (P : Finset α) (c : Finset α → κ) :
    totalWeight P c = (disjointPairs P c).card +
      (P.card - 3) * (trianglePairs P c).card := by
  classical
  rw [totalWeight_as_support_sum]
  have hterm : ∀ q ∈ equalPairs P c,
      ((P.powersetCard 4).filter (fun S => support q ⊆ S)).card =
      (if (support q).card = 3 then P.card - 3 else 0) +
      (if (support q).card = 4 then 1 else 0) := by
    intro q hq
    rcases support_card hq with h3 | h4
    · rw [card_four_supersets_three (support_subset hq) h3]
      simp [h3]
    · rw [card_four_supersets_four (support_subset hq) h4]
      simp [h4]
  simp_rw [sum_congr rfl hterm, sum_add_distrib]
  rw [← sum_filter, ← sum_filter]
  simp only [sum_const, Nat.nsmul_eq_mul, trianglePairs, disjointPairs]
  ring

omit [DecidableEq α] in
/-- Weighted counting is bounded below by the number of nonempty contributions. -/
theorem badCount_le_totalWeight (P : Finset α) (c : Finset α → κ) :
    badCount P c ≤ totalWeight P c := by
  classical
  unfold badCount badFourSets totalWeight
  rw [card_eq_sum_ones, sum_filter]
  apply sum_le_sum
  intro S _
  split_ifs with h
  · exact h
  · exact Nat.zero_le _

omit [DecidableEq α] in
/-- A pointwise bound scales only the bad four-sets, including the zero case. -/
theorem totalWeight_le_mul_badCount (P : Finset α) (c : Finset α → κ) (M : ℕ)
    (hM : ∀ S ∈ P.powersetCard 4, weight S c ≤ M) :
    totalWeight P c ≤ M * badCount P c := by
  classical
  unfold totalWeight badCount badFourSets
  rw [card_eq_sum_ones, sum_filter, mul_sum]
  apply sum_le_sum
  intro S hS
  split_ifs with h
  · simpa using hM S hS
  · simp only [mul_zero]
    omega

end Erdos1087
