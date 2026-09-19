/-
Copyright 2026. Released under the Apache 2.0 license.

The registered statement follows Formal Conjectures (Apache-2.0).
The known mathematical observation is recorded by Paul Erdős (1977).
Gott-L initiated and planned the project; Codex assisted with this proof.
-/

import E357Counting
import E357DensityBridge

namespace Erdos357

/-- The complete known infinite-sequence lower-density variant of Erdős 357. -/
theorem erdos_357.variants.infinite_set_lower_density
    (A : ℕ → ℕ) (hMono : StrictMono A) (hDistinct : HasDistinctSums A) :
    (Set.range A).lowerDensity = 0 := by
  apply le_antisymm ?_ (Set.lowerDensity_nonneg _)
  by_contra hn
  have hpos : 0 < (Set.range A).lowerDensity := lt_of_not_ge hn
  obtain ⟨C, hC, hBound⟩ := exists_linear_bound_of_lowerDensity_pos A hMono hpos
  exact no_linear_bound hDistinct hC hBound

#print axioms erdos_357.variants.infinite_set_lower_density

end Erdos357
