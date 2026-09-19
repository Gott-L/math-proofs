import Jsp399TripleCore

/-!
The two explicit increasing 27-element lists used in the numerical example.
This module verifies positivity, distinctness, and inequality of the sets.
The general parametric module supplies the subset-sum collision theorem.
Written with OpenAI Codex assistance, 2026-09-17. MIT license.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JSP399TwentySeven

def A (i : Index) : Nat :=
  [1,44,48,60,68,96,104,109,116,120,145,157,161,163,
   165,169,181,204,212,217,224,228,260,264,276,284,325][i.val]

def B (i : Index) : Nat :=
  [1,42,50,62,66,98,102,109,114,122,145,157,161,163,
   165,169,181,206,210,217,222,230,258,266,278,282,325][i.val]

theorem A_strict : ∀ i j : Index, i < j → A i < A j := by decide
theorem B_strict : ∀ i j : Index, i < j → B i < B j := by decide
theorem A_positive : ∀ i : Index, 0 < A i := by decide
theorem B_positive : ∀ i : Index, 0 < B i := by decide

theorem different_sets : ¬ (∀ x : Nat,
    (∃ i : Index, A i = x) ↔ (∃ j : Index, B j = x)) := by
  intro h
  have ha : ∃ i : Index, A i = 44 := ⟨1, rfl⟩
  obtain ⟨j, hj⟩ := (h 44).mp ha
  have hn : ∀ j : Index, B j ≠ 44 := by decide
  exact hn j hj


#print axioms A_strict
#print axioms B_strict
#print axioms A_positive
#print axioms B_positive
#print axioms different_sets

end JSP399TwentySeven
