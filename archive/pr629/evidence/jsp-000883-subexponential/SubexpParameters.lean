/-
Adapted from 56647563/awards PR601, commit 5130380a1d7f3ed00b827c666c79c89e202c3fdc,
submissions/jsp-000883/Parameters.lean and AsymptoticBound.lean, Apache-2.0.
Original formalization: 56647563 with Codex assistance.
Mathematical sources: Patrick White and Ricky Cipollini, with their stated AI collaborators.
Modifications: arbitrary root degree, a Nat.findGreatest construction for Lean 4.19,
and estimates uniform in each fixed degree. No new mathematical priority is claimed.
Gott-L: project initiation, objectives, planning and research direction.
Codex assistance: adaptation, proof extension and checks.
-/
import SizeBounds
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Linarith

set_option warningAsError true

namespace Erdos1063

def scale (d k : ℕ) : ℕ := Nat.findGreatest (fun t => t ^ d ≤ k) k
def center (d k : ℕ) : ℕ := k / (scale d k)^2 + 1
def cost (d k : ℕ) : ℕ := center d k + (2 * center d k * scale d k + k / (scale d k + 1))
def exponentCost (d k : ℕ) : ℕ := 3 + 2 * cost d k

theorem scale_pow_le {d : ℕ} (hd : 0 < d) (k : ℕ) : (scale d k)^d ≤ k := by
  apply Nat.findGreatest_spec (P := fun t => t ^ d ≤ k) (Nat.zero_le k)
  simp [hd.ne']

theorem scale_ge_of_pow_le {d k t : ℕ} (hd : 0 < d) (h : t^d ≤ k) :
    t ≤ scale d k := by
  exact Nat.le_findGreatest ((Nat.le_self_pow hd.ne' t).trans h) h

theorem lt_scale_succ_pow {d : ℕ} (hd : 0 < d) (k : ℕ) : k < (scale d k + 1)^d := by
  by_contra h
  have := scale_ge_of_pow_le hd (by omega : (scale d k + 1)^d ≤ k)
  omega

/-- The finite parameter arithmetic needs only fourth-power growth. -/
theorem parameter_arithmetic {t k : ℕ} (ht : 2 ≤ t) (hpow : t^4 ≤ k) :
    let E := k/t^2+1
    E < k ∧ k ≤ t^2*E ∧ k < (E+1)^2 ∧
      (E + (2*E*t + k/(t+1)))*t ≤ 7*k := by
  let E := k/t^2+1
  have ht0 : 0 < t := by omega
  have ht2 : 0 < t^2 := pow_pos ht0 _
  have h2 : t^2 ≤ k := le_trans (Nat.pow_le_pow_right ht0 (by decide : 2 ≤ 4)) hpow
  have hdiv : k/t^2*t^2 ≤ k := Nat.div_mul_le_self k (t^2)
  have hEprod : E*t^2 ≤ 2*k := by dsimp [E]; nlinarith
  have hEmod := Nat.mod_lt k ht2
  have hEdiv := Nat.div_add_mod k (t^2)
  have hkE : k < t^2*E := by dsimp [E]; nlinarith
  have hEge : t^2 ≤ E := by
    have hh : t^2 ≤ k/t^2 := (Nat.le_div_iff_mul_le ht2).mpr (by nlinarith [hpow])
    dsimp [E]
    omega
  have hfour : 4*E ≤ E*t^2 := by
    have hh := Nat.mul_le_mul_left E (by nlinarith : 4 ≤ t^2)
    simpa [Nat.mul_comm] using hh
  have hElt : E < k := by nlinarith
  have hy : k < (E+1)^2 := by nlinarith
  have hEt : E*t ≤ E*t^2 := Nat.mul_le_mul_left E (by nlinarith)
  have hquot : k/(t+1)*t ≤ k := le_trans
    (Nat.mul_le_mul_left (k/(t+1)) (by omega : t ≤ t+1)) (Nat.div_mul_le_self k (t+1))
  refine ⟨hElt, le_of_lt hkE, hy, ?_⟩
  change (E+(2*E*t+k/(t+1)))*t ≤ 7*k
  nlinarith

theorem scale_ge_two {d k : ℕ} (hd : 4 ≤ d) (hk : 2^d ≤ k) : 2 ≤ scale d k :=
  scale_ge_of_pow_le (by omega) hk

theorem scale_fourth_pow_le {d k : ℕ} (hd : 4 ≤ d) (hk : 2^d ≤ k) :
    (scale d k)^4 ≤ k := by
  have ht := scale_ge_two hd hk
  exact (Nat.pow_le_pow_right (by omega : 0 < scale d k) hd).trans
    (scale_pow_le (by omega) k)

theorem exponentCost_mul_scale {d k : ℕ} (hd : 4 ≤ d) (hk : 2^d ≤ k) :
    exponentCost d k * scale d k ≤ 17*k := by
  have ht := scale_ge_two hd hk
  have hc := (parameter_arithmetic ht (scale_fourth_pow_le hd hk)).2.2.2
  have htk : scale d k ≤ k := Nat.findGreatest_le k
  change cost d k * scale d k ≤ 7*k at hc
  unfold exponentCost
  nlinarith

/-- The degree-dependent parameters produce an actual interval with exactly
one failing coordinate, before any infimum or asymptotic comparison is used. -/
theorem parameter_witness {d k : ℕ} (hd : 4 ≤ d) (hk : 2^d ≤ k) :
    ∃ n : ℕ, 2*k ≤ n ∧
      (∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧ ∀ i < k, i ≠ i0 → n-i ∣ n.choose k) ∧
      n ≤ 4 * k^(exponentCost d k) * ((scale d k)^2)^(primeCount k) := by
  have ht := scale_ge_two hd hk
  have hp := parameter_arithmetic ht (scale_fourth_pow_le hd hk)
  have hk2 : 2 ≤ k := (Nat.le_self_pow (by omega : d ≠ 0) 2).trans hk
  exact exists_coarse_bounded_witness (M := scale d k) hk2
    hp.1 (pow_pos (by omega) _) hp.2.1 hp.2.2.1

end Erdos1063
