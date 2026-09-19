/-
Copyright 2026. Released under the Apache 2.0 license.
Explicit statement checks written for the internal cross-module review.
The reviewer adapted the reused finite modules but did not write the new
prime-count, parameter, asymptotic, minimum, or final submission proofs.
-/
import SubexpSubmission

open Finset Filter Asymptotics
open scoped Topology

namespace SubexpInternalReview

theorem admissible_definition (k n : ℕ) :
    Erdos1063.Admissible k n ↔
      2*k ≤ n ∧ ∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
        ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k := Iff.rfl

theorem minimum_definition (k : ℕ) :
    Erdos1063.leastWitness k =
      sInf {n : ℕ | 2*k ≤ n ∧ ∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
        ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k} := rfl

theorem prime_count_raw (k : ℕ) :
    (((range (k+1)).filter Nat.Prime).card : ℝ) * Real.log k ≤ 6*k :=
  Erdos1063.primeCount_mul_log_le k

theorem finite_bound_raw {E k y Q M : ℕ} (hk : 2 ≤ k) (hE : E < k)
    (hQ : 0 < Q) (hsize : k ≤ Q*E) (hy : k < (y+1)^2) :
    ∃ n : ℕ, 2*k ≤ n ∧
      (∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
        ∀ i < k, i ≠ i0 → n-i ∣ n.choose k) ∧
      n ≤ 4*k^(3+2*(y+(2*E*M+k/(M+1)))) *
        Q^((range (k+1)).filter Nat.Prime).card :=
  Erdos1063.exists_coarse_bounded_witness hk hE hQ hsize hy

theorem choose_degree_after_epsilon {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ, 4 ≤ d ∧ 12 / (d : ℝ) ≤ ε/2 :=
  Erdos1063.exists_degree_small_rate hε

theorem degree_then_threshold {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ, 4 ≤ d ∧ ∀ᶠ k : ℕ in atTop,
      ((4 * k^(Erdos1063.exponentCost d k) *
        ((Erdos1063.scale d k)^2)^(Erdos1063.primeCount k) : ℕ) : ℝ) ≤
          Real.exp (ε * k) :=
  Erdos1063.exists_subexponential_coarse_bound hε

/-- An explicit natural threshold for each positive real epsilon, with the
original binomial-block property written out rather than renamed. -/
theorem raw_witness_threshold : ∀ ε : ℝ, 0 < ε →
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → ∃ n : ℕ, 2*k ≤ n ∧
      (∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
        ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k) ∧
      (n : ℝ) ≤ Real.exp (ε * (k : ℝ)) := by
  intro ε hε
  exact eventually_atTop.mp (Erdos1063.subexponential_witness ε hε)

theorem raw_minimum_is_admissible (k : ℕ) (hk : 2 ≤ k) :
    let m := sInf {n : ℕ | 2*k ≤ n ∧ ∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
      ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k}
    2*k ≤ m ∧ ∃ i0 < k, ¬ (m-i0) ∣ m.choose k ∧
      ∀ i < k, i ≠ i0 → (m-i) ∣ m.choose k :=
  Erdos1063.leastWitness_spec hk

theorem raw_minimum_le (k n : ℕ)
    (hn : 2*k ≤ n ∧ ∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
      ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k) :
    sInf {m : ℕ | 2*k ≤ m ∧ ∃ i0 < k, ¬ (m-i0) ∣ m.choose k ∧
      ∀ i < k, i ≠ i0 → (m-i) ∣ m.choose k} ≤ n :=
  Erdos1063.leastWitness_le hn

theorem raw_minimum_subexponential : ∀ ε : ℝ, 0 < ε →
    ∀ᶠ k : ℕ in atTop,
      ((sInf {n : ℕ | 2*k ≤ n ∧ ∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
        ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k} : ℕ) : ℝ) ≤
          Real.exp (ε * (k : ℝ)) := by
  intro ε hε
  exact Erdos1063.leastWitness_subexponential ε hε

theorem raw_log_littleO :
    (fun k : ℕ => Real.log ((sInf {n : ℕ | 2*k ≤ n ∧
      ∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
        ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k} : ℕ) : ℝ))
      =o[atTop] (fun k : ℕ => (k : ℝ)) :=
  Erdos1063.erdos_1063.subexponential_upper

theorem raw_log_ratio_limit :
    Tendsto (fun k : ℕ =>
      Real.log ((sInf {n : ℕ | 2*k ≤ n ∧
        ∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
          ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k} : ℕ) : ℝ) / (k : ℝ))
      atTop (𝓝 (0 : ℝ)) :=
  Erdos1063.log_leastWitness_div_tendsto_zero

end SubexpInternalReview
