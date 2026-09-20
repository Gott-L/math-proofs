import Mathlib.Combinatorics.Hindman
import Mathlib.Data.PNat.Basic

/-!
# A nonprincipal additive idempotent on the positive integers

Ellis's compact-semigroup theorem supplies an additive idempotent ultrafilter.
It cannot be principal: an idempotent principal ultrafilter would give a
positive integer `a` with `a + a = a`.
-/

namespace GottL746

open Filter

attribute [local instance] Ultrafilter.addSemigroup

/-- Every additive idempotent ultrafilter on positive integers is cofinite. -/
theorem positive_idempotent_le_cofinite (U : Ultrafilter ℕ+) (hU : U + U = U) :
    (U : Filter ℕ+) ≤ cofinite := by
  rcases U.le_cofinite_or_eq_pure with hcofinite | ⟨a, ha⟩
  · exact hcofinite
  · have ha_mem : ∀ᶠ b in U, b = a := by simp [ha]
    have hsum : ∀ᶠ b in (U + U : Ultrafilter ℕ+), b = a := by
      simpa only [hU] using ha_mem
    have haa : a + a = a := by
      simpa [ha] using (Ultrafilter.eventually_add U U (fun b => b = a)).mp hsum
    have hn := congrArg (fun b : ℕ+ => (b : ℕ)) haa
    change (a : ℕ) + (a : ℕ) = (a : ℕ) at hn
    have hpos : 0 < (a : ℕ) := a.pos
    omega

/-- An additive idempotent on positive integers eventually exceeds every
natural-number bound. -/
theorem eventually_gt_nat (U : Ultrafilter ℕ+) (hU : U + U = U) (k : ℕ) :
    ∀ᶠ (n : ℕ+) in U, k < (n : ℕ) := by
  apply positive_idempotent_le_cofinite U hU
  apply Filter.eventually_cofinite.mpr
  have hfinite : {n : ℕ+ | (n : ℕ) ≤ k}.Finite :=
    (Set.finite_le_nat k).preimage fun _ _ _ _ h => Subtype.ext h
  simpa only [not_lt] using hfinite

/-- There is an additive idempotent ultrafilter on positive integers which
avoids every singleton. -/
theorem exists_positive_idempotent :
    ∃ U : Ultrafilter ℕ+, U + U = U ∧ ∀ a : ℕ+, ∀ᶠ b in U, b ≠ a := by
  obtain ⟨U, hU⟩ :=
    exists_idempotent_of_compact_t2_of_continuous_add_left
      (@Ultrafilter.continuous_add_left ℕ+ _)
  exact ⟨U, hU, Filter.le_cofinite_iff_eventually_ne.mp
    (positive_idempotent_le_cofinite U hU)⟩

end GottL746
