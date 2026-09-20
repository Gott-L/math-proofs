import Growth
import Rotation
import Coloring
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

/-!
A finite coloring of all integers avoiding all differences in an arbitrary
lacunary sequence. This new implementation follows the classical elementary
proof, with known earlier complete formalizations disclosed in STATUS.md.
-/

namespace GottL894

/-- Full positive-difference form of the lacunary coloring theorem. -/
theorem lacunary_difference_coloring (a : ℕ → ℕ)
    (hpos : ∀ k, 0 < a k)
    (hlac : ∃ ε : ℝ, 0 < ε ∧
      ∀ k, (1 + ε) * (a k : ℝ) ≤ (a (k + 1) : ℝ)) :
    ∃ N : ℕ, 0 < N ∧ ∃ c : ℤ → Fin N,
      ∀ x y : ℤ, ∀ k : ℕ, y - x = (a k : ℤ) → c x ≠ c y := by
  classical
  obtain ⟨ε, hε, hstep⟩ := hlac
  obtain ⟨r, hr, hstride⟩ := exists_stride a ε hε hstep
  have rotation_exists (i : Fin r) :
      ∃ θ : ℝ, ∀ j, ∃ z : ℤ,
        (z : ℝ) + 1 / 4 ≤ θ * (a (r * j + i.val) : ℝ) ∧
        θ * (a (r * j + i.val) : ℝ) ≤ (z : ℝ) + 3 / 4 :=
    exists_rotation (fun j => a (r * j + i.val))
      (fun j => hpos _) (stride_subsequence a r i.val hstride)
  let θ (i : Fin r) : ℝ := Classical.choose (rotation_exists i)
  have hθ (i : Fin r) := Classical.choose_spec (rotation_exists i)
  let localColor (i : Fin r) : ℤ → Fin 4 :=
    Classical.choose (rotation_coloring (θ i))
  have hlocal (i : Fin r) := Classical.choose_spec (rotation_coloring (θ i))
  let C := Fin r → Fin 4
  let encode : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
  let c : ℤ → Fin (Fintype.card C) := fun x => encode (fun i => localColor i x)
  refine ⟨Fintype.card C, Fintype.card_pos, c, ?_⟩
  intro x y k hdiff hsame
  let i : Fin r := ⟨k % r, Nat.mod_lt k hr⟩
  have hindex : r * (k / r) + i.val = k := by
    dsimp [i]
    simpa [Nat.add_comm] using Nat.mod_add_div k r
  obtain ⟨z, hzlo, hzhi⟩ := hθ i (k / r)
  have hmiddle : ∃ z : ℤ,
      (z : ℝ) + 1 / 4 ≤ θ i * ((y - x : ℤ) : ℝ) ∧
      θ i * ((y - x : ℤ) : ℝ) ≤ (z : ℝ) + 3 / 4 := by
    refine ⟨z, ?_, ?_⟩
    · simpa only [hdiff, Int.cast_natCast, hindex] using hzlo
    · simpa only [hdiff, Int.cast_natCast, hindex] using hzhi
  have hvector : (fun i => localColor i x) = (fun i => localColor i y) :=
    encode.injective hsame
  exact hlocal i y x hmiddle (congrFun hvector i).symm

end GottL894
