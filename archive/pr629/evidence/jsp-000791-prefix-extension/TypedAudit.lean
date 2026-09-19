import E951Extension

open scoped BigOperators
open MeasureTheory Set

-- Every finite strongly separated prefix, with no extra existence premise.
example {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 < a i) (hmono : StrictMono a)
    (hsep : ∀ u v : Fin n → ℕ, u ≠ v →
      1 ≤ |(∏ i, a i ^ u i) - (∏ i, a i ^ v i)|) :
    ∃ b : ℕ → ℝ, StrictMono b ∧ (∀ i, 1 < b i) ∧
      (∀ i : Fin n, b i = a i) ∧
      (∀ u v : ℕ →₀ ℕ, u ≠ v →
        1 ≤ |u.prod (fun i k => b i ^ k) - v.prod (fun i k => b i ^ k)|) :=
  E951.finite_prefix_extension a ha hmono hsep

-- A good next term can exceed any real cutoff.
example {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 < a i)
    (hsep : ∀ u v : Fin n → ℕ, u ≠ v →
      1 ≤ |(∏ i, a i ^ u i) - (∏ i, a i ^ v i)|) (B : ℝ) :
    ∃ x : ℝ, B < x ∧ 1 < x ∧
      (∀ u v : Fin (n + 1) → ℕ, u ≠ v →
        1 ≤ |(∏ i : Fin (n + 1), (Fin.snoc a x : Fin (n + 1) → ℝ) i ^ u i) -
          (∏ i : Fin (n + 1), (Fin.snoc a x : Fin (n + 1) → ℝ) i ^ v i)|) :=
  E951.extension_step a ha hsep B

-- Avoidance is proved for every old exponent vector, without separation input.
example {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 < a i) (B : ℝ) :
    ∃ x : ℝ, B < x ∧ 1 < x ∧
      (∀ u v : Fin n → ℕ, ∀ k : ℕ,
        1 ≤ |(∏ i, a i ^ u i) * x ^ (k + 1) - (∏ i, a i ^ v i)|) :=
  E951.exists_avoiding_above a ha B

example {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 < a i) :
    ∃ Z : ℝ, 0 < Z ∧ HasSum (fun u : Fin n → ℕ => (Real.sqrt (∏ i, a i ^ u i))⁻¹) Z :=
  E951.exists_hasSum_weight a ha

example (s t S : ℝ) (k : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) (hS : 4 ≤ S) :
    volume {x : ℝ | x ∈ Icc (S ^ 2) (2 * S ^ 2) ∧ |s * x ^ (k + 1) - t| < 1} ≤
      ENNReal.ofReal (8 * S ^ 2 * (2 / S) ^ (k + 1) / (Real.sqrt s * Real.sqrt t)) :=
  E951.badSet_volume_le s t S k hs ht hS

example (S : ℝ) (hS : 4 ≤ S) :
    (∑' k : ℕ, ENNReal.ofReal ((2 / S) ^ (k + 1))) ≤ ENNReal.ofReal (4 / S) :=
  E951.geometric_tail_bound S hS
