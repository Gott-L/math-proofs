/-
Copyright 2026. Released under the Apache License, Version 2.0.
Gott-L: project planning. Codex: Lean implementation.
Finite algebraic append step for the E951 sequence construction.
-/
import E951Defs

set_option warningAsError true

namespace E951

theorem monomial_snoc {n : ℕ} (a : Fin n → ℝ) (x : ℝ)
    (u : Fin (n + 1) → ℕ) :
    monomial (Fin.snoc a x) u =
      monomial a (fun i => u i.castSucc) * x ^ u (Fin.last n) := by
  simp [monomial, Fin.prod_univ_castSucc]

theorem separated_snoc {n : ℕ} (a : Fin n → ℝ) (x : ℝ)
    (_ha : ∀ i, 1 < a i) (hs : Separated a) (hx : 1 ≤ x)
    (hav : Avoids a x) : Separated (Fin.snoc a x) := by
  intro u v huv
  rw [monomial_snoc, monomial_snoc]
  have hp : ∀ k : ℕ, 1 ≤ x ^ k := fun k => one_le_pow₀ hx
  have hscale : ∀ (y : ℝ) (k : ℕ), 1 ≤ |y| → 1 ≤ |y * x ^ k| := by
    intro y k hy
    rw [abs_mul, abs_of_nonneg (by linarith [hp k] : 0 ≤ x ^ k)]
    nlinarith [hp k]
  rcases lt_trichotomy (u (Fin.last n)) (v (Fin.last n)) with hlt | heq | hgt
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    have hbase := hav (fun i => v i.castSucc) (fun i => u i.castSucc) k
    have he : monomial a (fun i => u i.castSucc) * x ^ u (Fin.last n) -
        monomial a (fun i => v i.castSucc) * x ^ v (Fin.last n) =
        -(monomial a (fun i => v i.castSucc) * x ^ (k + 1) -
          monomial a (fun i => u i.castSucc)) * x ^ u (Fin.last n) := by
      rw [hk, pow_add]
      ring
    rw [he]
    apply hscale
    simpa only [abs_neg] using hbase
  · have hne : (fun i : Fin n => u i.castSucc) ≠ (fun i => v i.castSucc) := by
      intro he
      apply huv
      funext i
      refine Fin.lastCases heq (fun j => congrFun he j) i
    have hbase := hs _ _ hne
    rw [heq, ← sub_mul]
    exact hscale _ _ hbase
  · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hgt
    have hbase := hav (fun i => u i.castSucc) (fun i => v i.castSucc) k
    have he : monomial a (fun i => u i.castSucc) * x ^ u (Fin.last n) -
        monomial a (fun i => v i.castSucc) * x ^ v (Fin.last n) =
        (monomial a (fun i => u i.castSucc) * x ^ (k + 1) -
          monomial a (fun i => v i.castSucc)) * x ^ v (Fin.last n) := by
      rw [hk, pow_add]
      ring
    rw [he]
    exact hscale _ _ hbase

end E951
