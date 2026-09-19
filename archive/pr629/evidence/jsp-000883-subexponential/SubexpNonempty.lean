/-
Copyright 2026. Released under the Apache 2.0 license.
Project initiation, objectives, planning and research direction: Gott-L.
Proof development, implementation and checks: Codex assistance.
This consequence uses the finite construction adapted from 56647563's PR601
and its credited mathematical sources. It guarantees that the minimum is
an actual admissible witness for every k >= 2, independently of asymptotics.
-/
import Simultaneous
import SubexpInfimum

set_option warningAsError true

namespace Erdos1063

theorem admissible_exists {k : ℕ} (hk : 2 ≤ k) : ∃ n, Admissible k n := by
  obtain ⟨n, hn, hprop, _⟩ := exists_bounded_witness (E := 1) (y := k) (Q := k)
    hk (by omega) (by omega) (by omega) (by nlinarith)
  exact ⟨n, hn, hprop⟩

theorem leastWitness_spec {k : ℕ} (hk : 2 ≤ k) : Admissible k (leastWitness k) :=
  leastWitness_spec_of_exists (admissible_exists hk)

theorem leastWitness_ge {k : ℕ} (hk : 2 ≤ k) : 2 * k ≤ leastWitness k :=
  (leastWitness_spec hk).1

end Erdos1063
