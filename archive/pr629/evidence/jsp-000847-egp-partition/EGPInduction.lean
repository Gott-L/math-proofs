/-
Copyright (c) 2026. Released under the Apache License, Version 2.0.
Project initiation, conception, objectives, planning and research direction: Gott-L.
Research, formal proof implementation and internal checks: Codex assistance.
Mathematical theorem: Erdos, Goodman and Posa (1966), Theorem 4.
-/
import EGPMatching
import EGPCount
import Mathlib.Data.Finset.Max

namespace EGP

variable {V : Type*}

theorem neighbors_subset (S : Finset V) (R : V → V → Prop) (v : V) :
    neighbors S R v ⊆ S := by
  classical
  exact Finset.filter_subset _ _

theorem exists_min_degree (S : Finset V) (R : V → V → Prop) (hne : S.Nonempty) :
    ∃ v ∈ S, ∀ u ∈ S, (neighbors S R v).card ≤ (neighbors S R u).card := by
  exact S.exists_min_image (fun v => (neighbors S R v).card) hne

theorem trim_symmetric (R : V → V → Prop) (M : Finset (Finset V))
    (hs : Symmetric R) : Symmetric (trim R M) := by
  intro a b hab
  refine ⟨hs hab.1, ?_⟩
  rintro ⟨e, he, hb, ha⟩
  exact hab.2 ⟨e, he, ha, hb⟩

theorem trim_irreflexive (R : V → V → Prop) (M : Finset (Finset V))
    (hi : Irreflexive R) : Irreflexive (trim R M) := by
  intro a ha
  exact hi a ha.1

theorem partition_empty (R : V → V → Prop) : PartitionOn ∅ R ∅ := by
  simp [PartitionOn]

/-- Strong induction closes the theorem once the explicit vertex extension is available. -/
theorem partition_bound_of_extension [DecidableEq V]
    (hext : ∀ (S : Finset V) (R : V → V → Prop) (v : V)
      (M Q : Finset (Finset V)), Symmetric R → Irreflexive R → v ∈ S →
      MatchingOn R (neighbors S R v) M → PartitionOn (S.erase v) (trim R M) Q →
      ∃ P, PartitionOn S R P ∧
        P.card ≤ Q.card + ((neighbors S R v).card - M.card))
    (S : Finset V) (R : V → V → Prop) (hs : Symmetric R) (hi : Irreflexive R) :
    ∃ P, PartitionOn S R P ∧ P.card ≤ S.card ^ 2 / 4 := by
  classical
  revert R
  refine Finset.strongInductionOn S ?_
  intro S ih
  intro R hs hi
  by_cases hne : S.Nonempty
  · obtain ⟨v, hv, hmin⟩ := exists_min_degree S R hne
    obtain ⟨M, hm, hmax⟩ := exists_maximal_matching R (neighbors S R v) hs hi
    have hcost : (neighbors S R v).card - M.card ≤ S.card / 2 := by
      apply matching_cost_le_half S (neighbors S R v) M R
        (neighbors_subset S R v) (matching_covered_subset hm) (matching_covered_card hm) hmax
      intro u hu
      exact hmin u ((neighbors_subset S R v) hu)
    obtain ⟨Q, hQ, hQcard⟩ := ih (S.erase v) (Finset.erase_ssubset hv)
      (trim R M) (trim_symmetric R M hs) (trim_irreflexive R M hi)
    obtain ⟨P, hP, hPcard⟩ := hext S R v M Q hs hi hv hm hQ
    refine ⟨P, hP, ?_⟩
    have hScard := Finset.card_erase_add_one hv
    calc
      P.card ≤ Q.card + ((neighbors S R v).card - M.card) := hPcard
      _ ≤ (S.erase v).card ^ 2 / 4 + S.card / 2 := Nat.add_le_add hQcard hcost
      _ = S.card ^ 2 / 4 := by
        rw [← hScard]
        exact floor_quarter_square_step _
  · have hS : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst S
    exact ⟨∅, partition_empty R, by simp⟩

end EGP
