import Main
import Family

set_option pp.universes true

#check GottL301.Powerful
#check GottL301.Consecutive
#check GottL301.CatalogClaim
#check GottL301.exists_consecutive_powerful_nonsquares
#check GottL301.exists_positive_consecutive_pair
#check GottL301.not_catalog_claim
#check GottL301.not_all_consecutive_powerful_have_square

#print axioms GottL301.powerful_square
#print axioms GottL301.powerful_cube
#print axioms GottL301.powerful_mul
#print axioms GottL301.not_isSquare_between
#print axioms GottL301.powerful_12167
#print axioms GottL301.powerful_12168
#print axioms GottL301.not_isSquare_12167
#print axioms GottL301.not_isSquare_12168
#print axioms GottL301.exists_consecutive_powerful_nonsquares
#print axioms GottL301.exists_positive_consecutive_pair
#print axioms GottL301.not_catalog_claim
#print axioms GottL301.not_all_consecutive_powerful_have_square

#check GottL301Family.infinite_consecutive_powerful_nonsquares
#print GottL301.Powerful
#print axioms GottL301Family.step_add_one
#print axioms GottL301Family.step_powerful
#print axioms GottL301Family.step_succ_powerful
#print axioms GottL301Family.step_mod_sixteen
#print axioms GottL301Family.square_mod_sixteen
#print axioms GottL301Family.nonsquares_of_mod_sixteen
#print axioms GottL301Family.lt_step
#print axioms GottL301Family.family_invariant
#print axioms GottL301Family.family_spec
#print axioms GottL301Family.family_strictMono
#print axioms GottL301Family.infinite_consecutive_powerful_nonsquares

-- Restate the complete infinite conclusion using the actual prime-divisor definition.
example : Set.Infinite {n : ℕ | 0 < n ∧
    (∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n) ∧
    (∀ p : ℕ, Nat.Prime p → p ∣ n + 1 → p ^ 2 ∣ n + 1) ∧
    ¬ IsSquare n ∧ ¬ IsSquare (n + 1)} := by
  apply GottL301Family.infinite_consecutive_powerful_nonsquares.mono
  intro n hn
  exact ⟨hn.1.1, hn.1.2, hn.2.1.2, hn.2.2⟩
