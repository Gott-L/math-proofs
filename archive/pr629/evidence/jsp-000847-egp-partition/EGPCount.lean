/-
Copyright (c) 2026. Released under the Apache 2.0 license.
Project initiation and research direction: Gott-L.
Formalization and checks: Codex assistance.

Counting lemmas for the classical Erdős–Goodman–Pósa edge-partition proof.
No mathematical discovery or global formalization priority is claimed.
-/
import EGPDefs
import Mathlib.Tactic.Ring

namespace EGP

variable {V : Type*} [DecidableEq V]

/-- A maximal matching in a minimum-degree neighborhood saves enough parts.
The maximality predicate already supplies the required orientation of R. -/
theorem matching_cost_le_half (S N : Finset V) (M : Finset (Finset V))
    (R : V → V → Prop) (hNS : N ⊆ S) (hcovered : covered M ⊆ N)
    (hcard : (covered M).card = 2 * M.card) (hmax : MaximalMatching R N M)
    (hmin : ∀ u ∈ N, N.card ≤ (neighbors S R u).card) :
    N.card - M.card ≤ S.card / 2 := by
  classical
  have hNSCard := Finset.card_le_card hNS
  have hMC : 2 * M.card ≤ N.card := by
    rw [← hcard]
    exact Finset.card_le_card hcovered
  by_cases hfull : N ⊆ covered M
  · have hNM : N.card ≤ 2 * M.card := by
      rw [← hcard]
      exact Finset.card_le_card hfull
    omega
  · obtain ⟨u, huN, huM⟩ := Finset.not_subset.mp hfull
    have hsub : neighbors S R u ⊆ (S \ N) ∪ covered M := by
      intro x hx
      obtain ⟨hxS, hux⟩ := Finset.mem_filter.mp hx
      by_cases hxN : x ∈ N
      · have hxM : x ∈ covered M := by
          by_contra hxM
          exact hmax u huN x hxN huM hxM hux
        exact Finset.mem_union_right _ hxM
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hxS, hxN⟩)
    have hdegree : (neighbors S R u).card ≤ S.card - N.card + 2 * M.card := by
      calc
        _ ≤ ((S \ N) ∪ covered M).card := Finset.card_le_card hsub
        _ ≤ (S \ N).card + (covered M).card := Finset.card_union_le _ _
        _ = S.card - N.card + 2 * M.card := by
          rw [Finset.card_sdiff hNS, hcard]
    have hdegMin := hmin u huN
    omega

/-- The exact floor recurrence used in the inductive edge-partition bound. -/
theorem floor_quarter_square_step (n : ℕ) :
    n ^ 2 / 4 + (n + 1) / 2 = (n + 1) ^ 2 / 4 := by
  let m := n / 2
  have hcases : n = 2 * m ∨ n = 2 * m + 1 := by
    have hrem := Nat.mod_lt n (show 0 < 2 by decide)
    have hdiv := Nat.div_add_mod n 2
    dsimp [m]
    omega
  rcases hcases with hn | hn
  · rw [hn]
    have hsq : (2 * m) ^ 2 = 4 * m ^ 2 := by ring
    have hnext : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 := by ring
    rw [hsq, hnext]
    omega
  · rw [hn]
    have hsq : (2 * m + 1) ^ 2 = 4 * (m ^ 2 + m) + 1 := by ring
    have hnext : (2 * m + 1 + 1) ^ 2 = 4 * (m ^ 2 + 2 * m + 1) := by ring
    rw [hsq, hnext]
    omega

#print axioms matching_cost_le_half
#print axioms floor_quarter_square_step

end EGP
