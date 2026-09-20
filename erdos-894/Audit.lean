import Main

-- Repeat the full original-problem statement without auxiliary hypotheses.
example (a : ℕ → ℕ) (hpos : ∀ k, 0 < a k)
    (hlac : ∃ ε : ℝ, 0 < ε ∧
      ∀ k, (1 + ε) * (a k : ℝ) ≤ (a (k + 1) : ℝ)) :
    ∃ N : ℕ, 0 < N ∧ ∃ c : ℤ → Fin N,
      ∀ x y : ℤ, ∀ k : ℕ, y - x = (a k : ℤ) → c x ≠ c y :=
  GottL894.lacunary_difference_coloring a hpos hlac

#print axioms GottL894.iterated_growth
#print axioms GottL894.exists_stride
#print axioms GottL894.stride_subsequence
#print axioms GottL894.exists_rotation
#print axioms GottL894.rotation_coloring
#print axioms GottL894.lacunary_difference_coloring
