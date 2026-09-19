/-
Copyright (c) 2026 Gott-L and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Known mathematical criterion: Erdos and Graham (1980), Theorem 1.
Gott-L initiated and directed the project; Codex implemented this proof.
The least-positive-difference argument constructs a finite list certificate.
-/
import E336Defs
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega

namespace E336

/-- An integer difference of two sums having the same number of terms in A. -/
def BalancedDifference (A : Set ℕ) (z : ℤ) : Prop :=
  ∃ xs ys : List ℕ, (∀ x ∈ xs, x ∈ A) ∧ (∀ y ∈ ys, y ∈ A) ∧
    xs.length = ys.length ∧ (xs.sum : ℤ) - (ys.sum : ℤ) = z

theorem balancedDifference_zero (A : Set ℕ) : BalancedDifference A 0 := by
  exact ⟨[], [], by simp, by simp, rfl, by simp⟩

theorem balancedDifference_add {A : Set ℕ} {u v : ℤ}
    (hu : BalancedDifference A u) (hv : BalancedDifference A v) :
    BalancedDifference A (u + v) := by
  rcases hu with ⟨xs, ys, hxs, hys, hlen, hsum⟩
  rcases hv with ⟨xs', ys', hxs', hys', hlen', hsum'⟩
  refine ⟨xs ++ xs', ys ++ ys', ?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hxs x hx
    · exact hxs' x hx
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact hys y hy
    · exact hys' y hy
  · simp only [List.length_append, hlen, hlen']
  · simp only [List.sum_append, Nat.cast_add]
    omega

theorem balancedDifference_neg {A : Set ℕ} {z : ℤ}
    (hz : BalancedDifference A z) : BalancedDifference A (-z) := by
  rcases hz with ⟨xs, ys, hxs, hys, hlen, hsum⟩
  exact ⟨ys, xs, hys, hxs, hlen.symm, by omega⟩

theorem balancedDifference_sub {A : Set ℕ} {u v : ℤ}
    (hu : BalancedDifference A u) (hv : BalancedDifference A v) :
    BalancedDifference A (u - v) := by
  simpa only [sub_eq_add_neg] using balancedDifference_add hu (balancedDifference_neg hv)

theorem balancedDifference_nat_mul {A : Set ℕ} {z : ℤ}
    (hz : BalancedDifference A z) (n : ℕ) : BalancedDifference A ((n : ℤ) * z) := by
  induction n with
  | zero => simpa using balancedDifference_zero A
  | succ n ih =>
    simpa only [Int.ofNat_succ, Int.add_mul, Int.one_mul] using
      balancedDifference_add ih hz

theorem balancedDifference_dist {A : Set ℕ} {x y : ℕ}
    (hx : x ∈ A) (hy : y ∈ A) : BalancedDifference A (Nat.dist x y : ℕ) := by
  rcases le_total x y with h | h
  · refine ⟨[y], [x], ?_, ?_, rfl, ?_⟩
    · simpa using hy
    · simpa using hx
    · simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.dist_eq_sub_of_le h]
      omega
  · refine ⟨[x], [y], ?_, ?_, rfl, ?_⟩
    · simpa using hx
    · simpa using hy
    · simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.dist_eq_sub_of_le_right h]
      omega

theorem balancedDifference_mod {A : Set ℕ} {v d : ℕ}
    (hv : BalancedDifference A (v : ℤ)) (hd : BalancedDifference A (d : ℤ)) :
    BalancedDifference A ((v % d : ℕ) : ℤ) := by
  have h := balancedDifference_sub hv (balancedDifference_nat_mul hd (v / d))
  have heq : (v : ℤ) - (v / d : ℕ) * (d : ℤ) = ((v % d : ℕ) : ℤ) := by
    have hdiv := Nat.mod_add_div v d
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) hdiv
    simp only [Int.ofNat_add, Int.ofNat_mul] at hcast
    rw [Int.mul_comm (d : ℤ) ((v / d : ℕ) : ℤ)] at hcast
    omega
  exact heq ▸ h

theorem differenceGcdOne_nonempty {A : Set ℕ} (hA : DifferenceGcdOne A) : A.Nonempty := by
  by_contra h
  have hzero := hA 0 (by
    intro x hx
    exact False.elim (h ⟨x, hx⟩))
  omega

theorem exists_positive_balancedDifference {A : Set ℕ} (hA : DifferenceGcdOne A) :
    ∃ d : ℕ, 0 < d ∧ BalancedDifference A (d : ℤ) := by
  by_contra h
  have hz : ∀ x ∈ A, ∀ y ∈ A, Nat.dist x y = 0 := by
    intro x hx y hy
    by_contra hn
    exact h ⟨Nat.dist x y, Nat.pos_of_ne_zero hn, balancedDifference_dist hx hy⟩
  have hzero := hA 0 (by
    intro x hx y hy
    rw [hz x hx y hy])
  omega

/-- The actual gcd-one hypothesis yields equal-length lists with sum difference one. -/
theorem balancedDifference_one {A : Set ℕ} (hA : DifferenceGcdOne A) :
    BalancedDifference A 1 := by
  classical
  let hex := exists_positive_balancedDifference hA
  let d := Nat.find hex
  have hd : 0 < d ∧ BalancedDifference A (d : ℤ) := Nat.find_spec hex
  have hdiv : ∀ x ∈ A, ∀ y ∈ A, d ∣ Nat.dist x y := by
    intro x hx y hy
    let v := Nat.dist x y
    have hv : BalancedDifference A (v : ℤ) := balancedDifference_dist hx hy
    have hm := balancedDifference_mod hv hd.2
    have hlt : v % d < d := Nat.mod_lt v hd.1
    have heq : v % d = 0 := by
      by_contra hn
      have hmin : d ≤ v % d := Nat.find_min' hex ⟨Nat.pos_of_ne_zero hn, hm⟩
      omega
    exact Nat.dvd_of_mod_eq_zero heq
  have heq : d = 1 := hA d hdiv
  simpa only [heq, Nat.cast_one] using hd.2

/-- A finite adjacent-length certificate, with no Bezout certificate as a premise. -/
theorem adjacentLengths_of_differenceGcdOne {A : Set ℕ} (hA : DifferenceGcdOne A) :
    AdjacentLengths A := by
  obtain ⟨a, ha⟩ := differenceGcdOne_nonempty hA
  have h := balancedDifference_nat_mul (balancedDifference_one hA) a
  simp only [mul_one] at h
  rcases h with ⟨xs, ys, hxs, hys, hlen, hsum⟩
  have hsum' : ys.sum + a = xs.sum := by omega
  refine ⟨xs.length, xs.sum, ⟨xs, rfl, hxs, rfl⟩, ?_⟩
  refine ⟨ys ++ [a], ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hys x hx
    · simpa using (List.mem_singleton.mp hx ▸ ha)
  · simpa using hsum'

end E336
