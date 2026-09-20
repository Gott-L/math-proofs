import Main

namespace GottL894

/-- A separately typed check of the unordered-distance interpretation. -/
theorem reviewC_absolute_difference (a : ℕ → ℕ)
    (hpos : ∀ k, 0 < a k)
    (hlac : ∃ ε : ℝ, 0 < ε ∧
      ∀ k, (1 + ε) * (a k : ℝ) ≤ (a (k + 1) : ℝ)) :
    ∃ N : ℕ, 0 < N ∧ ∃ c : ℤ → Fin N,
      ∀ x y : ℤ, ∀ k : ℕ, |x - y| = (a k : ℤ) → c x ≠ c y := by
  obtain ⟨N, hN, c, hc⟩ := lacunary_difference_coloring a hpos hlac
  refine ⟨N, hN, c, ?_⟩
  intro x y k hdiff
  rcases le_total x y with hxy | hyx
  · rw [abs_of_nonpos (sub_nonpos.mpr hxy)] at hdiff
    exact hc x y k (by omega)
  · rw [abs_of_nonneg (sub_nonneg.mpr hyx)] at hdiff
    exact (hc y x k hdiff).symm

end GottL894

#check GottL894.lacunary_difference_coloring
#print axioms GottL894.iterated_growth
#print axioms GottL894.exists_stride
#print axioms GottL894.exists_rotation
#print axioms GottL894.lacunary_difference_coloring
#print axioms GottL894.reviewC_absolute_difference
