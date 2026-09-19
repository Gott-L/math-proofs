/-
Copyright 2026. Released under the Apache License, Version 2.0.
Internal statement checks by the Append/Sequence contributor.
The other five modules were authored by other agents; this is not external review.
-/
import E951Extension

set_option warningAsError true
open scoped BigOperators ENNReal
open Set MeasureTheory

namespace E951InternalReview

theorem raw_final {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 < a i)
    (hm : ∀ ⦃i j⦄, i < j → a i < a j)
    (hs : ∀ u v : Fin n → ℕ, u ≠ v →
      1 ≤ |(∏ i, a i ^ u i) - (∏ i, a i ^ v i)|) :
    ∃ b : ℕ → ℝ, (∀ ⦃i j⦄, i < j → b i < b j) ∧ (∀ i, 1 < b i) ∧
      (∀ i : Fin n, b i = a i) ∧
      (∀ u v : ℕ →₀ ℕ, u ≠ v →
        1 ≤ |u.prod (fun i k => b i ^ k) - v.prod (fun i k => b i ^ k)|) :=
  E951.finite_prefix_extension a ha hm hs

theorem raw_avoiding {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 < a i) (B : ℝ) :
    ∃ x : ℝ, B < x ∧ 1 < x ∧
      ∀ u v : Fin n → ℕ, ∀ k : ℕ,
        1 ≤ |(∏ i, a i ^ u i) * x ^ (k + 1) - (∏ i, a i ^ v i)| :=
  E951.exists_avoiding_above a ha B

theorem raw_one_step {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 < a i)
    (hs : ∀ u v : Fin n → ℕ, u ≠ v →
      1 ≤ |(∏ i, a i ^ u i) - (∏ i, a i ^ v i)|) (B : ℝ) :
    ∃ x : ℝ, B < x ∧ 1 < x ∧
      ∀ u v : Fin (n + 1) → ℕ, u ≠ v →
        1 ≤ |(∏ i, Fin.snoc (α := fun _ => ℝ) a x i ^ u i) -
          (∏ i, Fin.snoc (α := fun _ => ℝ) a x i ^ v i)| :=
  E951.extension_step a ha hs B

theorem finite_products_injective {n : ℕ} {a : Fin n → ℝ}
    (hs : E951.Separated a) :
    Function.Injective (fun u : Fin n → ℕ => ∏ i, a i ^ u i) := by
  intro u v he
  change (∏ i, a i ^ u i) = (∏ i, a i ^ v i) at he
  by_contra hne
  have h := hs u v hne
  change 1 ≤ |(∏ i, a i ^ u i) - (∏ i, a i ^ v i)| at h
  rw [he, sub_self, abs_zero] at h
  norm_num at h

theorem sequence_products_injective {a : ℕ → ℝ} (hs : E951.SequenceSeparated a) :
    Function.Injective (fun u : ℕ →₀ ℕ => u.prod (fun i k => a i ^ k)) := by
  intro u v he
  change u.prod (fun i k => a i ^ k) = v.prod (fun i k => a i ^ k) at he
  by_contra hne
  have h := hs u v hne
  change 1 ≤ |u.prod (fun i k => a i ^ k) - v.prod (fun i k => a i ^ k)| at h
  rw [he, sub_self, abs_zero] at h
  norm_num at h

theorem raw_support_restriction (a : ℕ → ℝ) (u : ℕ →₀ ℕ) (N : ℕ)
    (hu : u.support ⊆ Finset.range N) :
    u.prod (fun i k => a i ^ k) = ∏ i : Fin N, a i ^ u i :=
  E951.sequenceMonomial_eq_prefix a u N hu

theorem raw_weight_sum {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 < a i) :
    ∃ Z : ℝ, 0 < Z ∧ HasSum
      (fun u : Fin n → ℕ => (Real.sqrt (∏ i, a i ^ u i))⁻¹) Z :=
  E951.exists_hasSum_weight a ha

theorem raw_geometric_bound (S : ℝ) (hS : 4 ≤ S) :
    (∑' k : ℕ, ENNReal.ofReal ((2 / S) ^ (k + 1))) ≤ ENNReal.ofReal (4 / S) :=
  E951.geometric_tail_bound S hS

theorem raw_bad_measure (s t S : ℝ) (k : ℕ)
    (hs : 1 ≤ s) (ht : 1 ≤ t) (hS : 4 ≤ S) :
    volume {x : ℝ | x ∈ Icc (S ^ 2) (2 * S ^ 2) ∧ |s * x ^ (k + 1) - t| < 1} ≤
      ENNReal.ofReal (8 * S ^ 2 * (2 / S) ^ (k + 1) /
        (Real.sqrt s * Real.sqrt t)) :=
  E951.badSet_volume_le s t S k hs ht hS

theorem raw_union_measure {n : ℕ} (a : Fin n → ℝ) (Z S : ℝ)
    (ha : ∀ i, 1 < a i) (hZ : 0 ≤ Z)
    (hzsum : HasSum (fun u : Fin n → ℕ => (Real.sqrt (∏ i, a i ^ u i))⁻¹) Z)
    (hS : 4 ≤ S) :
    volume (⋃ u : Fin n → ℕ, ⋃ v : Fin n → ℕ, ⋃ k : ℕ,
      {x : ℝ | x ∈ Icc (S ^ 2) (2 * S ^ 2) ∧
        |(∏ i, a i ^ u i) * x ^ (k + 1) - (∏ i, a i ^ v i)| < 1}) ≤
      ENNReal.ofReal (32 * S * Z ^ 2) :=
  E951.forbiddenUnion_volume_le a Z S ha hZ hzsum hS

theorem raw_empty_prefix :
    ∃ b : ℕ → ℝ, StrictMono b ∧ (∀ i, 1 < b i) ∧
      ∀ u v : ℕ →₀ ℕ, u ≠ v →
        1 ≤ |u.prod (fun i k => b i ^ k) - v.prod (fun i k => b i ^ k)| := by
  let a : Fin 0 → ℝ := Fin.elim0
  have hp : ∀ i, 1 < a i := fun i => Fin.elim0 i
  have hm : StrictMono a := fun i => Fin.elim0 i
  have hs : E951.Separated a := by
    intro u v hne
    exact False.elim (hne (Subsingleton.elim u v))
  obtain ⟨b, hmono, hpos, _, hsep⟩ := E951.finite_prefix_extension a hp hm hs
  exact ⟨b, hmono, hpos, hsep⟩

theorem empty_exponent_product (a : ℕ → ℝ) :
    E951.sequenceMonomial a (0 : ℕ →₀ ℕ) = 1 := by
  simp [E951.sequenceMonomial]

end E951InternalReview
