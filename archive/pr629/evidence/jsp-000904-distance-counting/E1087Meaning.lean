/-
Copyright 2026. Released under the Apache 2.0 license.
Independent formalization with Codex assistance for Gott-L's project.
This file checks the meaning of repeated-edge counts; it does not assume
any extremal or asymptotic result about Erdős Problem 1087.
-/
import E1087Core

open Finset

namespace Erdos1087

variable {α κ : Type*} [DecidableEq α]

theorem pair_mem_equalPairs_iff {P e f : Finset α} (c : Finset α → κ)
    (hef : e ≠ f) :
    {e, f} ∈ equalPairs P c ↔ e ∈ edges P ∧ f ∈ edges P ∧ c e = c f := by
  classical
  rw [mem_equalPairs]
  simp only [insert_subset_iff, singleton_subset_iff, card_pair hef,
    mem_insert, mem_singleton, forall_eq_or_imp, forall_eq, and_true, true_and]
  exact ⟨fun h => ⟨h.1.1, h.1.2, h.2.1⟩,
    fun h => ⟨⟨h.1, h.2.1⟩, h.2.2, h.2.2.symm⟩⟩

theorem weight_pos_iff (S : Finset α) (c : Finset α → κ) :
    0 < weight S c ↔ ∃ e ∈ edges S, ∃ f ∈ edges S, e ≠ f ∧ c e = c f := by
  classical
  rw [weight, card_pos]
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨e, f, hef, rfl⟩ := card_eq_two.mp (mem_equalPairs.mp hq).2.1
    have h := (pair_mem_equalPairs_iff c hef).mp hq
    exact ⟨e, h.1, f, h.2.1, hef, h.2.2⟩
  · rintro ⟨e, he, f, hf, hef, hcf⟩
    exact ⟨{e, f}, (pair_mem_equalPairs_iff c hef).mpr ⟨he, hf, hcf⟩⟩

theorem weight_pos_iff_card_image_lt [DecidableEq κ] (S : Finset α) (c : Finset α → κ) :
    0 < weight S c ↔ ((edges S).image c).card < (edges S).card := by
  classical
  have hle : ((edges S).image c).card ≤ (edges S).card := card_image_le
  have himg : ((edges S).image c).card < (edges S).card ↔
      ¬ Set.InjOn c (edges S : Set (Finset α)) := by
    rw [lt_iff_le_and_ne, and_iff_right hle, ne_eq, card_image_iff]
  rw [himg, weight_pos_iff]
  constructor
  · rintro ⟨e, he, f, hf, hef, hcf⟩ hinj
    exact hef (hinj he hf hcf)
  · intro hn
    simp only [Set.InjOn, mem_coe] at hn
    push_neg at hn
    obtain ⟨e, he, f, hf, hcf, hef⟩ := hn
    exact ⟨e, he, f, hf, hef, hcf⟩

theorem four_set_degenerate_iff [DecidableEq κ] (S : Finset α) (c : Finset α → κ)
    (hS : S.card = 4) :
    0 < weight S c ↔ ((edges S).image c).card < 6 := by
  have hE : (edges S).card = 6 := by rw [edges, card_powersetCard, hS]; decide
  rw [weight_pos_iff_card_image_lt, hE]

/-- For a triangle-supported pair, the shared endpoint is unique. -/
theorem triangle_pair_unique_apex {P : Finset α} {c : Finset α → κ}
    {q : Finset (Finset α)} (hq : q ∈ trianglePairs P c) :
    ∃ e f a, e ≠ f ∧ q = {e, f} ∧ e ∩ f = {a} := by
  classical
  obtain ⟨hmem, hcard⟩ := mem_filter.mp hq
  obtain ⟨e, f, hef, hqeq⟩ := card_eq_two.mp (mem_equalPairs.mp hmem).2.1
  subst q
  have h := (pair_mem_equalPairs_iff c hef).mp hmem
  have he := (mem_edges.mp h.1).2
  have hf := (mem_edges.mp h.2.1).2
  rw [support_pair] at hcard
  have hi : (e ∩ f).card = 1 := by
    have := card_union_add_card_inter e f
    omega
  obtain ⟨a, ha⟩ := card_eq_one.mp hi
  exact ⟨e, f, a, hef, rfl, ha⟩

end Erdos1087
