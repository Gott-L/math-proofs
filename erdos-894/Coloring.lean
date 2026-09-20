import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Init
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
An independently written four-color rotation construction for Erdős 894.
Known prior complete formalizations are disclosed in STATUS.md; this file
does not claim mathematical novelty or first formalization.
-/

namespace GottL894

/-- The index of a quarter interval, reduced modulo four. -/
noncomputable def quarterColor (θ : ℝ) (x : ℤ) : Fin 4 :=
  ⟨(Int.floor (4 * θ * (x : ℝ))).natMod 4, Int.natMod_lt (by decide)⟩

/-- A rotation whose difference lies in the closed middle half of a unit
interval separates the corresponding integer vertices with four colors. -/
theorem rotation_coloring (θ : ℝ) :
    ∃ c : ℤ → Fin 4, ∀ x y : ℤ,
      (∃ z : ℤ, (z : ℝ) + 1 / 4 ≤ θ * ((x - y : ℤ) : ℝ) ∧
        θ * ((x - y : ℤ) : ℝ) ≤ (z : ℝ) + 3 / 4) → c x ≠ c y := by
  refine ⟨quarterColor θ, ?_⟩
  intro x y hxy hcolor
  obtain ⟨z, hlo, hhi⟩ := hxy
  let a : ℤ := Int.floor (4 * θ * (x : ℝ))
  let b : ℤ := Int.floor (4 * θ * (y : ℝ))
  have hmodNat : a.natMod 4 = b.natMod 4 := congrArg Fin.val hcolor
  have hmod : a % 4 = b % 4 := by
    unfold Int.natMod at hmodNat
    have ha := Int.emod_nonneg a (by norm_num : (4 : ℤ) ≠ 0)
    have hb := Int.emod_nonneg b (by norm_num : (4 : ℤ) ≠ 0)
    omega
  have hax : (a : ℝ) ≤ 4 * θ * (x : ℝ) := Int.floor_le _
  have hxa : 4 * θ * (x : ℝ) < (a : ℝ) + 1 := Int.lt_floor_add_one _
  have hby : (b : ℝ) ≤ 4 * θ * (y : ℝ) := Int.floor_le _
  have hyb : 4 * θ * (y : ℝ) < (b : ℝ) + 1 := Int.lt_floor_add_one _
  rw [Int.cast_sub] at hlo hhi
  have hl : (4 : ℝ) * z < (a : ℝ) - b := by nlinarith
  have hu : (a : ℝ) - b < (4 : ℝ) * z + 4 := by nlinarith
  have hl' : 4 * z < a - b := by exact_mod_cast hl
  have hu' : a - b < 4 * z + 4 := by exact_mod_cast hu
  omega

end GottL894
