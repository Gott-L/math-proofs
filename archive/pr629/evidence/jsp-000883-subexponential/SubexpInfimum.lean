/-
Copyright 2026. Released under the Apache 2.0 license.
Original minimum definition: Copyright 2026 The Formal Conjectures Authors.
Project initiation, objectives, planning and research direction: Gott-L.
Proof development, implementation and checks: Codex assistance.
The binomial-block minimum follows the Formal Conjectures Authors' Erdős 1063
definition and 56647563's PR601. The subexponential mathematics is credited
to Patrick White and Ricky Cipollini, with their stated AI collaborators.
-/
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Defs

set_option warningAsError true

namespace Erdos1063
open Filter Asymptotics

/-- An actual block with exactly one nondivisor, in the original natural
number formulation; this predicate includes the required lower bound. -/
def Admissible (k n : ℕ) : Prop :=
  2 * k ≤ n ∧ ∃ i0 < k, ¬ (n - i0) ∣ n.choose k ∧
    ∀ i < k, i ≠ i0 → (n - i) ∣ n.choose k

noncomputable def leastWitness (k : ℕ) : ℕ := sInf {n : ℕ | Admissible k n}

theorem leastWitness_le {k n : ℕ} (hn : Admissible k n) : leastWitness k ≤ n :=
  Nat.sInf_le hn

/-- Membership of the minimum is used only after an actual witness has
established nonemptiness. -/
theorem leastWitness_spec_of_exists {k : ℕ} (h : ∃ n, Admissible k n) :
    Admissible k (leastWitness k) := Nat.sInf_mem h

theorem eventually_leastWitness_exp_of_witnesses {ε : ℝ}
    (h : ∀ᶠ k : ℕ in atTop, ∃ n, Admissible k n ∧ (n : ℝ) ≤ Real.exp (ε * k)) :
    ∀ᶠ k : ℕ in atTop, (leastWitness k : ℝ) ≤ Real.exp (ε * k) := by
  filter_upwards [h] with k hk
  obtain ⟨n, hn, hb⟩ := hk
  have hle : (leastWitness k : ℝ) ≤ (n : ℝ) := by exact_mod_cast leastWitness_le hn
  exact hle.trans hb

/-- A standard consequence of the quantified witness bound. The premise is
discharged by the finite construction and parameter estimates in the final
submission module; it is not an additional conjecture. -/
theorem log_leastWitness_isLittleO_of_witnesses
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop,
      ∃ n, Admissible k n ∧ (n : ℝ) ≤ Real.exp (ε * k)) :
    (fun k : ℕ => Real.log (leastWitness k : ℝ)) =o[atTop] fun k : ℕ => (k : ℝ) := by
  apply IsLittleO.of_bound
  intro ε hε
  filter_upwards [h ε hε, eventually_ge_atTop 2] with k hk hk2
  obtain ⟨n, hn, hb⟩ := hk
  have hspec := leastWitness_spec_of_exists ⟨n, hn⟩
  have hleast : (1 : ℝ) ≤ leastWitness k := by
    have hbound : 1 ≤ leastWitness k := by have := hspec.1; omega
    exact_mod_cast hbound
  have hle : (leastWitness k : ℝ) ≤ (n : ℝ) := by exact_mod_cast leastWitness_le hn
  have hbound : (leastWitness k : ℝ) ≤ Real.exp (ε * k) := hle.trans hb
  have hlog := Real.log_le_log (by linarith : (0 : ℝ) < leastWitness k) hbound
  rw [Real.log_exp] at hlog
  simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hleast),
    abs_of_nonneg (Nat.cast_nonneg k : (0 : ℝ) ≤ _)] using hlog

end Erdos1063
