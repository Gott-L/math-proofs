/-
Adapted and extended from 56647563/awards PR601, commit
5130380a1d7f3ed00b827c666c79c89e202c3fdc, AsymptoticBound.lean, Apache-2.0.
Original fixed-rate formalization: 56647563 with Codex assistance.
Mathematical subexponential conclusion: Patrick White and Ricky Cipollini,
with their stated AI collaborators. This file claims a stronger formal endpoint,
not a new mathematical discovery or global priority.
Gott-L: project initiation, objectives, planning and research direction.
Codex assistance: adaptation, proof extension and checks.
-/
import SubexpParameters
import PrimeCountBound
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option warningAsError true

namespace Erdos1063
open Filter Real Asymptotics
open scoped Topology

/-- The anchor contribution has arbitrarily small linear cost for every
fixed root degree. The hypotheses here are discharged by the next theorem. -/
theorem anchor_log_bound {d k : ℕ} (hd : 4 ≤ d) (hk : 2^d ≤ k)
    {δ : ℝ} (hδ : 0 < δ)
    (hsmall : log ((scale d k : ℝ) + 1) ≤
      (δ / (68 * (d : ℝ))) * ((scale d k : ℝ) + 1))
    (hconst : log 4 ≤ (δ / 2) * k) :
    log 4 + (exponentCost d k : ℝ) * log k ≤ δ * k := by
  have ht := scale_ge_two hd hk
  have htR : (2 : ℝ) ≤ scale d k := by exact_mod_cast ht
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hkpos : 0 < k := lt_of_lt_of_le (pow_pos (by decide : 0 < (2 : ℕ)) d) hk
  have hpow : (k : ℝ) ≤ ((scale d k : ℝ) + 1)^d := by
    exact_mod_cast le_of_lt (lt_scale_succ_pow (by omega : 0 < d) k)
  have hlog := log_le_log (by exact_mod_cast hkpos : (0 : ℝ) < k) hpow
  rw [log_pow] at hlog
  have hcoef : (d : ℝ) * (δ / (68 * (d : ℝ))) = δ / 68 := by
    field_simp
    ring
  have hsmall' := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  rw [← mul_assoc, hcoef] at hsmall'
  have hlogSmall : log (k : ℝ) ≤ (δ / 34) * (scale d k : ℝ) := by
    nlinarith
  have hc : (exponentCost d k : ℝ) * (scale d k : ℝ) ≤ 17 * (k : ℝ) := by
    exact_mod_cast exponentCost_mul_scale hd hk
  have hmul := mul_le_mul_of_nonneg_left hlogSmall
    (Nat.cast_nonneg (exponentCost d k) : (0 : ℝ) ≤ _)
  have hcost := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ δ / 34)
  nlinarith only [hmul, hcost, hconst]

theorem eventually_anchor_log_bound {d : ℕ} (hd : 4 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop,
      log 4 + (exponentCost d k : ℝ) * log k ≤ δ * k := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hη : 0 < δ / (68 * (d : ℝ)) := by positivity
  have hreal := Real.isLittleO_log_id_atTop.bound hη
  have hnat : ∀ᶠ t : ℕ in atTop,
      ‖log (t : ℝ)‖ ≤ (δ / (68 * (d : ℝ))) * ‖(t : ℝ)‖ :=
    tendsto_natCast_atTop_atTop.eventually hreal
  obtain ⟨N, hN⟩ := eventually_atTop.mp hnat
  have hconst : ∀ᶠ k : ℕ in atTop, 2 * log 4 / δ ≤ (k : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop (2 * log 4 / δ))
  filter_upwards [eventually_ge_atTop (2^d), eventually_ge_atTop (N^d), hconst]
    with k hk hkN hkconst
  apply anchor_log_bound hd hk hδ
  · have ht : N ≤ scale d k + 1 := by
      have := scale_ge_of_pow_le (by omega : 0 < d) hkN
      omega
    have hb := hN (scale d k + 1) ht
    have hlog0 : 0 ≤ log (((scale d k + 1 : ℕ) : ℝ)) :=
      log_nonneg (by exact_mod_cast (show 1 ≤ scale d k + 1 by omega))
    rw [Real.norm_eq_abs, abs_of_nonneg hlog0, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg (scale d k + 1) : (0 : ℝ) ≤ _)] at hb
    simpa only [Nat.cast_add, Nat.cast_one] using hb
  · have h := (div_le_iff₀ hδ).mp hkconst
    linarith

/-- A linear bound on prime-count times log gives a cost inversely
proportional to the freely chosen root degree. -/
theorem prime_log_bound_of_count {d k P : ℕ} (hd : 4 ≤ d) (hk : 2^d ≤ k)
    (hP : (P : ℝ) * log k ≤ 6 * k) :
    (P : ℝ) * log ((scale d k : ℝ)^2) ≤ (12 / (d : ℝ)) * k := by
  have ht := scale_ge_two hd hk
  have ht0 : (0 : ℝ) < scale d k := by exact_mod_cast (show 0 < scale d k by omega)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hlog := log_le_log (pow_pos ht0 d)
    (show (scale d k : ℝ)^d ≤ k by exact_mod_cast scale_pow_le (by omega : 0 < d) k)
  rw [log_pow] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg P : (0 : ℝ) ≤ P)
  have hmain : ((P : ℝ) * log ((scale d k : ℝ)^2)) * (d : ℝ) ≤ 12 * k := by
    rw [log_pow]
    norm_num
    nlinarith only [hmul, hP]
  have hdiv := (le_div_iff₀ hd0).mpr hmain
  convert hdiv using 1
  ring

theorem prime_log_bound {d k : ℕ} (hd : 4 ≤ d) (hk : 2^d ≤ k) :
    (primeCount k : ℝ) * log ((scale d k : ℝ)^2) ≤ (12 / (d : ℝ)) * k :=
  prime_log_bound_of_count hd hk (primeCount_mul_log_le k)

def coarseBound (d k : ℕ) : ℕ :=
  4 * k^(exponentCost d k) * ((scale d k)^2)^(primeCount k)

/-- Every fixed degree gives an exponential rate whose prime contribution
is at most 12/d and whose anchor contribution is arbitrarily small. -/
theorem eventually_coarse_bound {d : ℕ} (hd : 4 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ k : ℕ in atTop,
      (coarseBound d k : ℝ) ≤ exp ((δ + 12 / (d : ℝ)) * k) := by
  filter_upwards [eventually_anchor_log_bound hd hδ, eventually_ge_atTop (2^d)]
    with k ha hk
  have ht := scale_ge_two hd hk
  have hkpos : 0 < k := lt_of_lt_of_le (pow_pos (by decide : 0 < (2 : ℕ)) d) hk
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hkpos
  have ht0 : (0 : ℝ) < scale d k := by exact_mod_cast (show 0 < scale d k by omega)
  have hcb : (0 : ℝ) < coarseBound d k := by
    unfold coarseBound
    push_cast
    positivity
  have he : log (coarseBound d k : ℝ) = log 4 + (exponentCost d k : ℝ) * log k +
      (primeCount k : ℝ) * log ((scale d k : ℝ)^2) := by
    unfold coarseBound
    push_cast
    rw [log_mul (by positivity) (by positivity), log_mul (by norm_num) (by positivity),
      log_pow, log_pow]
  have hp := prime_log_bound hd hk
  have hlog : log (coarseBound d k : ℝ) ≤ (δ + 12 / (d : ℝ)) * k := by
    rw [he]
    nlinarith only [ha, hp]
  have hexp := exp_le_exp.mpr hlog
  rwa [exp_log hcb] at hexp

theorem exists_degree_small_rate {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ, 4 ≤ d ∧ 12 / (d : ℝ) ≤ ε / 2 := by
  obtain ⟨d, hd⟩ := exists_nat_gt (max 4 (24 / ε))
  have hdR : (4 : ℝ) < d := lt_of_le_of_lt (le_max_left _ _) hd
  have hd4 : 4 ≤ d := by exact_mod_cast le_of_lt hdR
  have hd0 : (0 : ℝ) < d := by linarith
  have h24 : 24 < (d : ℝ) * ε :=
    (div_lt_iff₀ hε).mp (lt_of_le_of_lt (le_max_right _ _) hd)
  refine ⟨d, hd4, (div_le_iff₀ hd0).mpr ?_⟩
  nlinarith

/-- The degree is chosen after epsilon; it is not one fixed positive
exponential rate renamed as a subexponential bound. -/
theorem exists_subexponential_coarse_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ d : ℕ, 4 ≤ d ∧ ∀ᶠ k : ℕ in atTop,
      (coarseBound d k : ℝ) ≤ exp (ε * k) := by
  obtain ⟨d, hd, hrate⟩ := exists_degree_small_rate hε
  refine ⟨d, hd, ?_⟩
  filter_upwards [eventually_coarse_bound hd (half_pos hε)] with k hk
  apply hk.trans (exp_le_exp.mpr ?_)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hr : ε / 2 + 12 / (d : ℝ) ≤ ε := by linarith
  exact mul_le_mul_of_nonneg_right hr hk0

/-- For every positive exponential rate there are, eventually, actual
binomial-divisibility witnesses below that rate. No residue, prime-interval,
nonemptiness, or previously assumed witness premise remains. -/
theorem subexponential_witness (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∃ n : ℕ, 2*k ≤ n ∧
      (∃ i0 < k, ¬ (n-i0) ∣ n.choose k ∧ ∀ i < k, i ≠ i0 → n-i ∣ n.choose k) ∧
      (n : ℝ) ≤ exp (ε * k) := by
  obtain ⟨d, hd, hbound⟩ := exists_subexponential_coarse_bound hε
  filter_upwards [hbound, eventually_ge_atTop (2^d)] with k hb hk
  obtain ⟨n, hn, hw, hsize⟩ := parameter_witness hd hk
  refine ⟨n, hn, hw, ?_⟩
  have hnc : (n : ℝ) ≤ (coarseBound d k : ℝ) := by exact_mod_cast hsize
  exact hnc.trans hb

end Erdos1063
