import Main
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Monotone.Basic

/-!
An infinite family strengthening the consecutive powerful nonsquare witness of
JSP-000301. This is classical Pell-type mathematics, not a new discovery; see
Walker (1976), Lemmas 3.3--3.4 and Theorem 3.5, pp. 114--116.

The polynomial step below is the odd-power construction for consecutive
square-multiple solutions. Gott-L directed the project; Codex wrote this module.
It imports the independently written local Main for the definition of Powerful,
its elementary closure lemmas, and the initial pair 12167, 12168. It imports no
other problem-specific formalization and makes no priority or award claim.
The result below is infinitude, not an asymptotic counting theorem for E365.
-/

namespace GottL301Family

open GottL301

/-- The polynomial form of the odd-power Pell transformation. -/
def step (n : ℕ) : ℕ := n * (4 * n + 3) ^ 2

/-- Both consecutive entries are multiplied by positive squares. -/
theorem step_add_one (n : ℕ) :
    step n + 1 = (n + 1) * (4 * n + 1) ^ 2 := by
  unfold step
  ring

theorem step_powerful {n : ℕ} (hn : Powerful n) : Powerful (step n) := by
  exact powerful_mul hn (powerful_square (by positivity))

theorem step_succ_powerful {n : ℕ} (hn : Powerful (n + 1)) :
    Powerful (step n + 1) := by
  rw [step_add_one]
  exact powerful_mul hn (powerful_square (by positivity))

/-- This residue simultaneously excludes squares at `n` and `n+1`. -/
theorem step_mod_sixteen {n : ℕ} (hn : n % 16 = 7) : step n % 16 = 7 := by
  norm_num [step, Nat.mul_mod, Nat.add_mod, Nat.pow_mod, hn]

/-- A finite residue calculation, proved by kernel reduction. -/
theorem square_mod_sixteen {n : ℕ} (hn : IsSquare n) :
    n % 16 ≠ 7 ∧ n % 16 ≠ 8 := by
  obtain ⟨r, rfl⟩ := hn
  have h : ∀ a : Fin 16, (a.val * a.val) % 16 ≠ 7 ∧
      (a.val * a.val) % 16 ≠ 8 := by decide
  simpa only [Nat.mul_mod, Nat.mod_mod] using
    h ⟨r % 16, Nat.mod_lt _ (by decide)⟩

theorem nonsquares_of_mod_sixteen {n : ℕ} (hn : n % 16 = 7) :
    ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := by
  have hn1 : (n + 1) % 16 = 8 := by
    norm_num [Nat.add_mod, hn]
  exact ⟨fun h => (square_mod_sixteen h).1 hn,
    fun h => (square_mod_sixteen h).2 hn1⟩

theorem lt_step {n : ℕ} (hn : 0 < n) : n < step n := by
  have hs : 1 < (4 * n + 3) ^ 2 := by nlinarith
  calc n = n * 1 := (Nat.mul_one n).symm
    _ < n * (4 * n + 3) ^ 2 := Nat.mul_lt_mul_of_pos_left hs hn
    _ = step n := rfl

/-- Start at `23^3 = 12167`, whose successor is `2^3 * 39^2`. -/
def family : ℕ → ℕ
  | 0 => 12167
  | k + 1 => step (family k)

theorem family_invariant (k : ℕ) :
    Powerful (family k) ∧ Powerful (family k + 1) ∧ family k % 16 = 7 := by
  induction k with
  | zero =>
      exact ⟨powerful_12167, powerful_12168, by norm_num [family]⟩
  | succ k ih =>
      exact ⟨step_powerful ih.1, step_succ_powerful ih.2.1,
        step_mod_sixteen ih.2.2⟩

theorem family_spec (k : ℕ) :
    Powerful (family k) ∧ Powerful (family k + 1) ∧
      ¬ IsSquare (family k) ∧ ¬ IsSquare (family k + 1) := by
  obtain ⟨hp, hp1, hmod⟩ := family_invariant k
  exact ⟨hp, hp1, nonsquares_of_mod_sixteen hmod⟩

theorem family_strictMono : StrictMono family := by
  apply strictMono_nat_of_lt_succ
  intro k
  exact lt_step (family_invariant k).1.1

/-- Infinitely many distinct consecutive powerful pairs have neither entry square. -/
theorem infinite_consecutive_powerful_nonsquares :
    Set.Infinite {n : ℕ | Powerful n ∧ Powerful (n + 1) ∧
      ¬ IsSquare n ∧ ¬ IsSquare (n + 1)} := by
  exact Set.infinite_of_injective_forall_mem family_strictMono.injective family_spec

end GottL301Family
