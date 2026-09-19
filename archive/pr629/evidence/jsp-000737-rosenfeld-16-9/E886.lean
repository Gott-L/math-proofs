/-
Copyright 2026. Released under the Apache 2.0 license.

The definition and compatibility statement follow Formal Conjectures,
Copyright 2026 The Formal Conjectures Authors (Apache-2.0).
The known lower construction is due to Erdős and Rosenfeld, with a prior
constant-64 formalization by Jarek Koch. This proof supplies constants 16 and 9.
Gott-L initiated and planned the project; Codex assisted with formalization.
-/

import E886Window
import Mathlib.NumberTheory.Divisors

namespace Erdos886

/-- The exact open divisor interval used by the public problem statement. -/
noncomputable def Erdos886Divisors (n : ℕ) (ε C : ℝ) : Finset ℕ :=
  (Nat.divisors n).filter (fun d =>
    (n : ℝ) ^ (1 / 2 : ℝ) < d ∧
      (d : ℝ) < (n : ℝ) ^ (1 / 2 : ℝ) + C * (n : ℝ) ^ (1 / 2 - ε))

theorem selected_mem_divisors {a d : ℕ} {C : ℝ}
    (ha : 1 ≤ a) (hdvd : d ∣ N a) (hlo : A0 a ≤ d) (hhi : d ≤ A3 a)
    (hu : (A3 a : ℝ) < Real.sqrt (N a : ℝ) + C * (N a : ℝ) ^ (1 / 4 : ℝ)) :
    d ∈ Erdos886Divisors (N a) (1 / 4) C := by
  apply Finset.mem_filter.mpr
  refine ⟨Nat.mem_divisors.mpr ⟨hdvd, (N_pos ha).ne'⟩, ?_⟩
  have hlor : (A0 a : ℝ) ≤ (d : ℝ) := by exact_mod_cast hlo
  have hhir : (d : ℝ) ≤ (A3 a : ℝ) := by exact_mod_cast hhi
  have hl := lt_of_lt_of_le (sqrt_bracket ha).2 hlor
  have hh := lt_of_le_of_lt hhir hu
  constructor
  · simpa only [← Real.sqrt_eq_rpow] using hl
  · simpa only [show (1 / 2 - 1 / 4 : ℝ) = 1 / 4 by norm_num,
      ← Real.sqrt_eq_rpow] using hh

/-- Four distinct explicitly factored divisors give the required count. -/
theorem four_count_of_upper {a : ℕ} {C : ℝ} (ha : 1 ≤ a)
    (hu : (A3 a : ℝ) < Real.sqrt (N a : ℝ) + C * (N a : ℝ) ^ (1 / 4 : ℝ)) :
    4 ≤ (Erdos886Divisors (N a) (1 / 4) C).card := by
  classical
  have h01 := A0_lt_A1 a
  have h12 := A1_lt_A2 a
  have h23 := A2_lt_A3 a
  have h02 := lt_trans h01 h12
  have h13 := lt_trans h12 h23
  have h03 := lt_trans h02 h23
  let S : Finset ℕ := {A0 a, A1 a, A2 a, A3 a}
  have hc : S.card = 4 := by
    simp [S, h01.ne, h02.ne, h03.ne, h12.ne, h13.ne, h23.ne]
  have hs : S ⊆ Erdos886Divisors (N a) (1 / 4) C := by
    intro d hd
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl | rfl
    · exact selected_mem_divisors ha (A0_dvd_N a) le_rfl h03.le hu
    · exact selected_mem_divisors ha (A1_dvd_N a) h01.le h13.le hu
    · exact selected_mem_divisors ha (A2_dvd_N a) h02.le h23.le hu
    · exact selected_mem_divisors ha (A3_dvd_N a) h03.le le_rfl hu
  rw [← hc]
  exact Finset.card_le_card hs

theorem four_count16 {a : ℕ} (ha : 10 ≤ a) :
    4 ≤ (Erdos886Divisors (N a) (1 / 4) 16).card :=
  four_count_of_upper (by omega) (A3_lt_upper16 ha)

theorem four_count9 {a : ℕ} (ha : 66 ≤ a) :
    4 ≤ (Erdos886Divisors (N a) (1 / 4) 9).card :=
  four_count_of_upper (by omega) (A3_lt_upper9 ha)

/-- The complete known constant-16 variant from Formal Conjectures. -/
theorem erdos_886.variants.rosenfeld_infinite :
    Set.Infinite {n | 4 ≤ (Erdos886Divisors n (1 / 4) 16).card} := by
  apply Set.infinite_of_forall_exists_gt
  intro M
  let a := max 10 (M + 1)
  have ha : 10 ≤ a := le_max_left _ _
  have hM : M + 1 ≤ a := le_max_right _ _
  have han : a ≤ N a := self_le_N (by omega)
  exact ⟨N a, four_count16 ha, by omega⟩

/-- A narrower interval still contains four divisors for infinitely many inputs. -/
theorem rosenfeld_infinite9 :
    Set.Infinite {n | 4 ≤ (Erdos886Divisors n (1 / 4) 9).card} := by
  apply Set.infinite_of_forall_exists_gt
  intro M
  let a := max 66 (M + 1)
  have ha : 66 ≤ a := le_max_left _ _
  have hM : M + 1 ≤ a := le_max_right _ _
  have han : a ≤ N a := self_le_N (by omega)
  exact ⟨N a, four_count9 ha, by omega⟩

#print axioms erdos_886.variants.rosenfeld_infinite
#print axioms rosenfeld_infinite9

end Erdos886
