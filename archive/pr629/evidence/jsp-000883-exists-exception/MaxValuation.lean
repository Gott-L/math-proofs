/-
Copyright 2026. Released under the Apache 2.0 license.

An independent implementation prepared with Codex assistance.
This elementary lemma is part of a formalization of the known
Erdős–Selfridge binomial divisibility observation; no mathematical
discovery or first-formalization priority is asserted.
-/

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Dist

namespace Erdos1063

/-- If the prime valuation of `b` is at most that of `a`, their nonzero
distance has at least the prime valuation of `b`. -/
theorem factorization_le_dist_of_le {a b p : ℕ}
    (hp : p.Prime) (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : a ≠ b) (hle : b.factorization p ≤ a.factorization p) :
    b.factorization p ≤ (Nat.dist a b).factorization p := by
  apply (hp.pow_dvd_iff_le_factorization (Nat.dist_pos_of_ne hne).ne').mp
  have hpa : p ^ b.factorization p ∣ a :=
    (hp.pow_dvd_iff_le_factorization ha).mpr hle
  have hpb : p ^ b.factorization p ∣ b :=
    (hp.pow_dvd_iff_le_factorization hb).mpr le_rfl
  change p ^ b.factorization p ∣ a - b + (b - a)
  exact Nat.dvd_add (Nat.dvd_sub hpa hpb) (Nat.dvd_sub hpb hpa)

/-- Reflecting two offsets within the same natural-number interval
preserves their distance. -/
theorem dist_sub_sub_of_le {n i j : ℕ} (hi : i ≤ n) (hj : j ≤ n) :
    Nat.dist (n - i) (n - j) = Nat.dist i j := by
  calc
    Nat.dist (n - i) (n - j) = Nat.dist j i :=
      Nat.dist_eq_intro (by rw [Nat.sub_add_cancel hi, Nat.sub_add_cancel hj])
    _ = Nat.dist i j := Nat.dist_comm j i

/-- The preceding valuation bound specialized to two distinct offsets
in a positive descending block. -/
theorem factorization_le_offset_dist {n i j p : ℕ}
    (hp : p.Prime) (hi : i < n) (hj : j < n) (hij : i ≠ j)
    (hle : (n - j).factorization p ≤ (n - i).factorization p) :
    (n - j).factorization p ≤ (Nat.dist i j).factorization p := by
  have hne : n - i ≠ n - j := by
    intro h
    apply hij
    apply Nat.eq_of_dist_eq_zero
    rw [← dist_sub_sub_of_le hi.le hj.le]
    exact Nat.dist_eq_zero h
  have h := factorization_le_dist_of_le hp
    (Nat.sub_ne_zero_of_lt hi) (Nat.sub_ne_zero_of_lt hj) hne hle
  rwa [dist_sub_sub_of_le hi.le hj.le] at h

end Erdos1063
