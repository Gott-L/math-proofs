/-
Copyright 2026. Released under the Apache 2.0 license.
Original minimum definition: Copyright 2026 The Formal Conjectures Authors.
Project initiation, objectives, planning and research direction: Gott-L.
Proof extension, implementation and checks: Codex assistance.
Mathematical subexponential result: Patrick White and Ricky Cipollini,
with their stated AI collaborators. Reused finite formalization:
56647563 with Codex assistance, PR601 commit 5130380a1d7f3ed00b827c666c79c89e202c3fdc.
This packet extends that fixed exponential-rate formalization to every
positive rate. It makes no mathematical discovery or global priority claim.
-/
import SubexpAsymptotic
import SubexpNonempty
import Mathlib.Analysis.Asymptotics.Lemmas

set_option warningAsError true

namespace Erdos1063
open Filter Asymptotics
open scoped Topology

theorem admissible_subexponential_witness (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∃ n, Admissible k n ∧ (n : ℝ) ≤ Real.exp (ε * k) := by
  filter_upwards [subexponential_witness ε hε] with k hk
  obtain ⟨n, hn, hprop, hb⟩ := hk
  exact ⟨n, ⟨hn, hprop⟩, hb⟩

/-- The actual least admissible binomial block grows more slowly than every
fixed positive exponential rate. -/
theorem leastWitness_subexponential (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, (leastWitness k : ℝ) ≤ Real.exp (ε * k) :=
  eventually_leastWitness_exp_of_witnesses (admissible_subexponential_witness ε hε)

/-- A subexponential upper bound on the actual Erdős 1063 minimum. All finite
witness, prime-count, and parameter hypotheses have been discharged. -/
theorem erdos_1063.subexponential_upper :
    (fun k : ℕ => Real.log (leastWitness k : ℝ)) =o[atTop] fun k : ℕ => (k : ℝ) :=
  log_leastWitness_isLittleO_of_witnesses admissible_subexponential_witness

theorem log_leastWitness_div_tendsto_zero :
    Tendsto (fun k : ℕ => Real.log (leastWitness k : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
  erdos_1063.subexponential_upper.tendsto_div_nhds_zero

#print axioms admissible_exists
#print axioms leastWitness_spec
#print axioms subexponential_witness
#print axioms leastWitness_subexponential
#print axioms erdos_1063.subexponential_upper
#print axioms log_leastWitness_div_tendsto_zero

end Erdos1063
