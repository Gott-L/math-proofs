import SubexpSubmission

open Filter Asymptotics Erdos1063
open scoped Topology

example (k n : ℕ) : Admissible k n ↔
    2*k ≤ n ∧ ∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
      ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k := Iff.rfl

example (k : ℕ) : leastWitness k =
    sInf {n : ℕ | 2*k ≤ n ∧ ∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
      ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k} := rfl

example (k : ℕ) (hk : 2 ≤ k) :
    ∃ n : ℕ, 2*k ≤ n ∧ ∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
      ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k := admissible_exists hk

example (k : ℕ) (hk : 2 ≤ k) :
    2*k ≤ leastWitness k ∧ ∃ i0 < k,
      ¬ (leastWitness k-i0) ∣ (leastWitness k).choose k ∧
      ∀ i < k, i ≠ i0 → (leastWitness k-i) ∣ (leastWitness k).choose k :=
  leastWitness_spec hk

example (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k : ℕ in atTop,
    ∃ n : ℕ, 2*k ≤ n ∧
      (∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
        ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k) ∧
      (n : ℝ) ≤ Real.exp (ε*k) := subexponential_witness ε hε

example (ε : ℝ) (hε : 0 < ε) : ∀ᶠ k : ℕ in atTop,
    ((sInf {n : ℕ | 2*k ≤ n ∧ ∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧
      ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k} : ℕ) : ℝ) ≤ Real.exp (ε*k) :=
  leastWitness_subexponential ε hε

example : (fun k : ℕ => Real.log (leastWitness k : ℝ)) =o[atTop]
    fun k : ℕ => (k : ℝ) := erdos_1063.subexponential_upper

example : Tendsto (fun k : ℕ => Real.log (leastWitness k : ℝ) / (k : ℝ))
    atTop (𝓝 0) := log_leastWitness_div_tendsto_zero

example (k : ℕ) : (((Finset.range (k+1)).filter Nat.Prime).card : ℝ) *
    Real.log k ≤ 6*k := primeCount_mul_log_le k

example {E k y Q M : ℕ} (hk : 2 ≤ k) (hE : E < k)
    (hQ : 0 < Q) (hsize : k ≤ Q*E) (hy : k < (y+1)^2) :
    ∃ n : ℕ, 2*k ≤ n ∧
      (∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧ ∀ i < k, i ≠ i0 → (n-i) ∣ n.choose k) ∧
      n ≤ 4*k^(3+2*(y+(2*E*M+k/(M+1)))) * Q^(primeCount k) :=
  exists_coarse_bounded_witness hk hE hQ hsize hy
