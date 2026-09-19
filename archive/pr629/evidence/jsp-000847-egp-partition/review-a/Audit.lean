/-
Copyright 2026. Released under the Apache License, Version 2.0.
Internal statement checks by the matching-module contributor, reviewing the
other proof modules and the fully assembled endpoints. Not external review.
-/
import EGPGraph

namespace EGPInternalReview

theorem clique_definition {V : Type*} (R : V → V → Prop) (p : Finset V) :
    EGP.Clique R p ↔ ∀ a ∈ p, ∀ b ∈ p, a ≠ b → R a b := Iff.rfl

theorem partition_definition {V : Type*} (S : Finset V) (R : V → V → Prop)
    (P : Finset (Finset V)) :
    EGP.PartitionOn S R P ↔
      (∀ p ∈ P, p ⊆ S ∧ (p.card = 2 ∨ p.card = 3) ∧
        ∀ a ∈ p, ∀ b ∈ p, a ≠ b → R a b) ∧
      ∀ a ∈ S, ∀ b ∈ S, R a b →
        ∃! p, p ∈ P ∧ a ∈ p ∧ b ∈ p := Iff.rfl

/-- The finite-set endpoint has only the stated simple-relation hypotheses. -/
theorem raw_finite_set {V : Type*} (S : Finset V) (R : V → V → Prop)
    (hs : ∀ a b, R a b → R b a) (hi : ∀ a, ¬ R a a) :
    ∃ P : Finset (Finset V), P.card ≤ S.card ^ 2 / 4 ∧
      (∀ p ∈ P, p ⊆ S ∧ (p.card = 2 ∨ p.card = 3) ∧
        ∀ a ∈ p, ∀ b ∈ p, a ≠ b → R a b) ∧
      (∀ a ∈ S, ∀ b ∈ S, R a b →
        ∃! p, p ∈ P ∧ a ∈ p ∧ b ∈ p) := by
  obtain ⟨P, hP, hb⟩ := EGP.erdos_goodman_posa S R hs hi
  exact ⟨P, hb, hP.1, hP.2⟩

theorem raw_fin_n (n : ℕ) (R : Fin n → Fin n → Prop)
    (hs : ∀ a b, R a b → R b a) (hi : ∀ a, ¬ R a a) :
    ∃ P : Finset (Finset (Fin n)), P.card ≤ n ^ 2 / 4 ∧
      (∀ p ∈ P, (p.card = 2 ∨ p.card = 3) ∧
        ∀ a ∈ p, ∀ b ∈ p, a ≠ b → R a b) ∧
      (∀ a b, R a b → ∃! p, p ∈ P ∧ a ∈ p ∧ b ∈ p) :=
  EGP.finite_relation_partition n R hs hi

theorem raw_simple_graph {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ P : Finset (Finset V), P.card ≤ Fintype.card V ^ 2 / 4 ∧
      (∀ p ∈ P, (p.card = 2 ∨ p.card = 3) ∧
        ∀ a ∈ p, ∀ b ∈ p, a ≠ b → G.Adj a b) ∧
      (∀ a b, G.Adj a b → ∃! p, p ∈ P ∧ a ∈ p ∧ b ∈ p) :=
  EGP.simple_graph_partition G

/-- Expanding unique existence gives an actual owner and excludes every
different candidate owner; this is stronger than a clique cover. -/
theorem explicit_unique_ownership {V : Type*} {S : Finset V}
    {R : V → V → Prop} {P : Finset (Finset V)} (hP : EGP.PartitionOn S R P) :
    ∀ a ∈ S, ∀ b ∈ S, R a b →
      ∃ p, p ∈ P ∧ a ∈ p ∧ b ∈ p ∧
        ∀ q, q ∈ P → a ∈ q → b ∈ q → q = p := by
  intro a ha b hb hab
  obtain ⟨p, hp, hu⟩ := hP.2 a ha b hb hab
  exact ⟨p, hp.1, hp.2.1, hp.2.2,
    fun q hq haq hbq => hu q ⟨hq, haq, hbq⟩⟩

/-- Different parts cannot share two different vertices. -/
theorem different_parts_no_common_edge {V : Type*} {S : Finset V}
    {R : V → V → Prop} {P : Finset (Finset V)} (hP : EGP.PartitionOn S R P)
    {p q : Finset V} (hp : p ∈ P) (hq : q ∈ P) (hpq : p ≠ q)
    {a b : V} (hap : a ∈ p) (hbp : b ∈ p) (haq : a ∈ q) (hbq : b ∈ q) : a = b := by
  by_contra hab
  have hR : R a b := (hP.1 p hp).2.2 a hap b hbp hab
  obtain ⟨w, _, hu⟩ := hP.2 a ((hP.1 p hp).1 hap) b ((hP.1 p hp).1 hbp) hR
  exact hpq ((hu p ⟨hp, hap, hbp⟩).trans (hu q ⟨hq, haq, hbq⟩).symm)

theorem raw_floor_recurrence (n : ℕ) :
    n ^ 2 / 4 + (n + 1) / 2 = (n + 1) ^ 2 / 4 :=
  EGP.floor_quarter_square_step n

end EGPInternalReview
