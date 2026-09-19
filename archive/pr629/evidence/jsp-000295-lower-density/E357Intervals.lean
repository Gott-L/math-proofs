/-
Copyright 2025 The Formal Conjectures Authors.
Copyright 2026. Additional proofs prepared with Codex assistance.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

The generic HasDistinctSums definition is reproduced verbatim from
FormalConjectures/ErdosProblems/357.lean at commit
40e7c98697de6f66b8cbdbf641749ab39ed9c152. The interval lemmas below
are an independently written implementation of elementary facts.
-/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Erdos357

def HasDistinctSums {ι α : Type*} [Preorder ι] [AddCommMonoid α] (a : ι → α) : Prop :=
  {J : Finset ι | (J : Set ι).OrdConnected}.InjOn (fun J ↦ ∑ x ∈ J, a x)

/-- The sum of the `r` consecutive terms beginning at index `j`. -/
def blockSum (A : ℕ → ℕ) (j r : ℕ) : ℕ :=
  ∑ u ∈ Finset.Ico j (j + r), A u

/-- Distinct positive-length blocks have different sums. -/
theorem blockSum_injective {A : ℕ → ℕ} (hDistinct : HasDistinctSums A)
    {j k r s : ℕ} (hr : 0 < r) (hs : 0 < s)
    (hSum : blockSum A j r = blockSum A k s) : j = k ∧ r = s := by
  have hIntervals : Finset.Ico j (j + r) = Finset.Ico k (k + s) :=
    hDistinct (by simpa only [Set.mem_setOf_eq, Finset.coe_Ico] using
      (Set.ordConnected_Ico : (Set.Ico j (j + r)).OrdConnected))
      (by simpa only [Set.mem_setOf_eq, Finset.coe_Ico] using
        (Set.ordConnected_Ico : (Set.Ico k (k + s)).OrdConnected)) hSum
  have hj : j ∈ Finset.Ico j (j + r) := by
    simp only [Finset.mem_Ico]
    omega
  have hk : k ∈ Finset.Ico k (k + s) := by
    simp only [Finset.mem_Ico]
    omega
  rw [hIntervals] at hj
  rw [← hIntervals] at hk
  have hjk : j = k := Nat.le_antisymm (Finset.mem_Ico.mp hk).1
    (Finset.mem_Ico.mp hj).1
  have hrs : r = s := by
    simpa only [Nat.card_Ico, Nat.add_sub_cancel_left] using
      congrArg Finset.card hIntervals
  exact ⟨hjk, hrs⟩

/-- A termwise linear upper bound controls every block sum.
No monotonicity assumption is needed for this estimate. -/
theorem blockSum_le_of_linear_bound {A : ℕ → ℕ} {C : ℕ}
    (hBound : ∀ u, A u ≤ C * (u + 1)) (j r : ℕ) :
    blockSum A j r ≤ C * r * (j + r) := by
  calc
    blockSum A j r ≤ ∑ _u ∈ Finset.Ico j (j + r), C * (j + r) := by
      apply Finset.sum_le_sum
      intro u hu
      exact (hBound u).trans (Nat.mul_le_mul_left C
        (Nat.succ_le_of_lt (Finset.mem_Ico.mp hu).2))
    _ = C * r * (j + r) := by
      simp only [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left,
        Nat.nsmul_eq_mul]
      ac_rfl

end Erdos357

#print axioms Erdos357.blockSum_injective
#print axioms Erdos357.blockSum_le_of_linear_bound
