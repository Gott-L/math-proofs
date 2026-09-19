/-
Copyright 2026 Gott-L and the E951 formalization contributors.
Released under Apache 2.0 license as described in the file LICENSE.

The known finite-prefix extension argument is discussed by Barreto--Price
and by Patrick White + Claude, Erdős Problem a Day, report 951 (2026-07-28).
This module is a fresh Lean implementation of its geometric-series input,
prepared with OpenAI Codex assistance. It makes no mathematical priority claim.
-/
import E951Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Instances.ENNReal.Lemmas

open scoped BigOperators

namespace E951

theorem monomial_ge_one {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 1 < a i) (u : Fin n → ℕ) : 1 ≤ monomial a u := by
  induction n with
  | zero => simp [monomial]
  | succ n ih =>
    rw [monomial, Fin.prod_univ_succ]
    exact one_le_mul_of_one_le_of_one_le
      (one_le_pow₀ (ha 0).le) (ih (fun i => ha i.succ) (fun i => u i.succ))

theorem monomial_pos {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 1 < a i) (u : Fin n → ℕ) : 0 < monomial a u :=
  lt_of_lt_of_le zero_lt_one (monomial_ge_one ha u)

theorem weight_pos {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 1 < a i) (u : Fin n → ℕ) : 0 < weight a u :=
  inv_pos.mpr (Real.sqrt_pos.mpr (monomial_pos ha u))

private theorem sqrt_nat_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    Real.sqrt (x ^ k) = Real.sqrt x ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg hx k), ih, pow_succ]

theorem weight_eq_prod {n : ℕ} {a : Fin n → ℝ}
    (ha : ∀ i, 1 < a i) (u : Fin n → ℕ) :
    weight a u = ∏ i, ((Real.sqrt (a i))⁻¹) ^ u i := by
  induction n with
  | zero => simp [weight, monomial]
  | succ n ih =>
    rw [weight, monomial, Fin.prod_univ_succ,
      Real.sqrt_mul (pow_nonneg (lt_trans zero_lt_one (ha 0)).le _),
      mul_inv_rev, sqrt_nat_pow (lt_trans zero_lt_one (ha 0)).le, ← inv_pow,
      Fin.prod_univ_succ]
    change weight (fun i => a i.succ) (fun i => u i.succ) *
      (Real.sqrt (a 0))⁻¹ ^ u 0 = _
    rw [ih (fun i => ha i.succ) (fun i => u i.succ), mul_comm]

private theorem hasSum_fin_geometric {n : ℕ} (q : Fin n → ℝ)
    (hzero : ∀ i, 0 ≤ q i) (hone : ∀ i, q i < 1) :
    HasSum (fun u : Fin n → ℕ => ∏ i, q i ^ u i)
      (∏ i, (1 - q i)⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hhead : HasSum (fun k : ℕ => q 0 ^ k) (1 - q 0)⁻¹ :=
      hasSum_geometric_of_lt_one (hzero 0) (hone 0)
    have htail : HasSum (fun u : Fin n → ℕ => ∏ i : Fin n, q i.succ ^ u i)
        (∏ i : Fin n, (1 - q i.succ)⁻¹) :=
      ih (fun i => q i.succ) (fun i => hzero i.succ) (fun i => hone i.succ)
    have htailnonneg : ∀ u : Fin n → ℕ, 0 ≤ ∏ i : Fin n, q i.succ ^ u i := by
      intro u
      exact Finset.prod_nonneg (fun i _ => pow_nonneg (hzero i.succ) _)
    have hsumprod : Summable
        (fun uv : ℕ × (Fin n → ℕ) => q 0 ^ uv.1 * ∏ i : Fin n, q i.succ ^ uv.2 i) :=
      Summable.mul_of_nonneg
        (f := fun k : ℕ => q 0 ^ k)
        (g := fun u : Fin n → ℕ => ∏ i : Fin n, q i.succ ^ u i)
        hhead.summable htail.summable
        (fun k : ℕ => pow_nonneg (hzero 0) k) htailnonneg
    have hprod : HasSum
        (fun uv : ℕ × (Fin n → ℕ) => q 0 ^ uv.1 * ∏ i : Fin n, q i.succ ^ uv.2 i)
        ((1 - q 0)⁻¹ * ∏ i : Fin n, (1 - q i.succ)⁻¹) :=
      HasSum.mul
        (f := fun k : ℕ => q 0 ^ k)
        (g := fun u : Fin n → ℕ => ∏ i : Fin n, q i.succ ^ u i)
        hhead htail hsumprod
    apply (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).hasSum_iff.mp
    simpa only [Function.comp_def, Fin.prod_univ_succ, Fin.consEquiv_apply,
      Fin.cons_zero, Fin.cons_succ] using hprod

/-- The sum of all inverse-square-root monomial weights is finite and positive.
No separation hypothesis is required. -/
theorem exists_hasSum_weight {n : ℕ} (a : Fin n → ℝ)
    (ha : ∀ i, 1 < a i) : ∃ Z : ℝ, 0 < Z ∧ HasSum (weight a) Z := by
  let q : Fin n → ℝ := fun i => (Real.sqrt (a i))⁻¹
  have hqpos : ∀ i, 0 < q i := fun i =>
    inv_pos.mpr (Real.sqrt_pos.mpr (lt_trans zero_lt_one (ha i)))
  have hqlt : ∀ i, q i < 1 := fun i =>
    inv_lt_one_of_one_lt₀ (by simpa using Real.sqrt_lt_sqrt zero_le_one (ha i))
  refine ⟨∏ i, (1 - q i)⁻¹, ?_, ?_⟩
  · exact Finset.prod_pos (fun i _ => inv_pos.mpr (sub_pos.mpr (hqlt i)))
  · have hfun : weight a = (fun u => ∏ i, q i ^ u i) := funext (weight_eq_prod ha)
    rw [hfun]
    exact hasSum_fin_geometric q (fun i => (hqpos i).le) hqlt

theorem summable_weight {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, 1 < a i) :
    Summable (weight a) := by
  obtain ⟨Z, _, hZ⟩ := exists_hasSum_weight a ha
  exact hZ.summable

/-- Transfer the real sum to the nonnegative extended reals used by volume. -/
theorem tsum_ofReal_weight {n : ℕ} {a : Fin n → ℝ} {Z : ℝ}
    (ha : ∀ i, 1 < a i) (hZ : HasSum (weight a) Z) :
    (∑' u, ENNReal.ofReal (weight a u)) = ENNReal.ofReal Z := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun u => (weight_pos ha u).le) hZ.summable,
    hZ.tsum_eq]

end E951
