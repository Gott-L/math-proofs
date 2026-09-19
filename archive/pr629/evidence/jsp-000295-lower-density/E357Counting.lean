/-
Copyright 2026. Released under the Apache 2.0 license.

An elementary dyadic counting proof of the known Erdős 357 observation.
Project initiation and research direction: Gott-L.
Mathematical reconstruction and Lean implementation: Codex assistance.
No mathematical novelty or first-formalization priority is asserted.
-/

import E357DyadicBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace Erdos357

/-- Distinct consecutive sums cannot coexist with a uniform linear bound
on the terms, even without a monotonicity hypothesis. -/
theorem no_linear_bound {A : ℕ → ℕ} (hDistinct : HasDistinctSums A)
    {C : ℕ} (hC : 0 < C) : ¬ (∀ n, A n ≤ C * (n + 1)) := by
  classical
  intro hBound
  let R := 4 * C + 1
  let q := 2 ^ (2 * R - 1)
  let I := (Finset.range R).biUnion (dyadicBlock R)
  have hR : 0 < R := by dsimp [R]; omega
  have hq : 0 < q := by dsimp [q]; positivity
  have hdisjoint : (Finset.range R : Set ℕ).PairwiseDisjoint (dyadicBlock R) := by
    intro t ht u hu htu
    exact dyadicBlock_disjoint R htu
  have hcard : I.card = R * q := by
    dsimp [I]
    rw [Finset.card_biUnion hdisjoint]
    have hs : (∑ t ∈ Finset.range R, (dyadicBlock R t).card) =
        (Finset.range R).card * q :=
      Finset.sum_const_nat (fun t ht => dyadicBlock_card (Finset.mem_range.mp ht))
    simpa only [Finset.card_range] using hs
  have hpos : ∀ x ∈ I, 0 < x.1 := by
    intro x hx
    obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
    exact dyadicBlock_length_pos hxt
  have hinj : Set.InjOn (fun x : ℕ × ℕ => blockSum A x.2 x.1) I := by
    intro x hx y hy hsum
    have hxy := blockSum_injective hDistinct (hpos x hx) (hpos y hy) hsum
    exact Prod.ext hxy.2 hxy.1
  have hsubset : I.image (fun x : ℕ × ℕ => blockSum A x.2 x.1) ⊆
      Finset.range (2 * C * 2 ^ (2 * R)) := by
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨t, ht, hxt⟩ := Finset.mem_biUnion.mp hx
    exact Finset.mem_range.mpr
      (dyadicBlock_sum_lt hC (Finset.mem_range.mp ht) hBound hxt)
  have hcount : R * q ≤ 2 * C * 2 ^ (2 * R) := by
    have h := Finset.card_le_card hsubset
    rw [Finset.card_image_of_injOn hinj, Finset.card_range, hcard] at h
    exact h
  have hp : 2 ^ (2 * R) = 2 * q := by
    calc
      2 ^ (2 * R) = 2 ^ ((2 * R - 1) + 1) := by
        exact congrArg (fun m : ℕ => 2 ^ m) (by omega)
      _ = 2 * q := by dsimp [q]; rw [pow_succ]; ac_rfl
  rw [hp] at hcount
  have hfinal : (4 * C + 1) * q ≤ 4 * C * q := by
    calc
      (4 * C + 1) * q = R * q := rfl
      _ ≤ 2 * C * (2 * q) := hcount
      _ = 4 * C * q := by ring
  nlinarith

#print axioms no_linear_bound

end Erdos357
