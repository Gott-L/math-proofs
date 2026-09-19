import E357

/- Internal review checks; these statements expand the imported predicates. -/

example {ι α : Type*} [Preorder ι] [AddCommMonoid α] (A : ι → α) :
    Erdos357.HasDistinctSums A ↔
      ∀ J K : Finset ι, (J : Set ι).OrdConnected → (K : Set ι).OrdConnected →
        (∑ x ∈ J, A x) = (∑ x ∈ K, A x) → J = K := by
  constructor
  · intro h J K hJ hK hs
    exact h hJ hK hs
  · intro h J hJ K hK hs
    exact h J K hJ hK hs

example {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S B : Set β) :
    S.lowerDensity B = Filter.atTop.liminf (fun b : β =>
      (((S ∩ B) ∩ Set.Iio b).ncard : ℝ) / ((B ∩ Set.Iio b).ncard : ℝ)) := rfl

/-- The exact registered theorem type. -/
example (A : ℕ → ℕ) (hMono : StrictMono A)
    (hDistinct : Erdos357.HasDistinctSums A) : (Set.range A).lowerDensity = 0 :=
  Erdos357.erdos_357.variants.infinite_set_lower_density A hMono hDistinct

/-- Expanded consecutive-block hypothesis and the original ambient-set liminf. -/
example (A : ℕ → ℕ) (hMono : StrictMono A)
    (hDistinct : ∀ J K : Finset ℕ,
      (J : Set ℕ).OrdConnected → (K : Set ℕ).OrdConnected →
      (∑ x ∈ J, A x) = (∑ x ∈ K, A x) → J = K) :
    Filter.atTop.liminf (fun b : ℕ =>
      ((((Set.range A ∩ Set.univ) ∩ Set.Iio b).ncard : ℝ) /
        ((Set.univ ∩ Set.Iio b).ncard : ℝ))) = 0 := by
  have hd : Erdos357.HasDistinctSums A := by
    intro J hJ K hK hs
    exact hDistinct J K hJ hK hs
  simpa only [Set.lowerDensity, Set.partialDensity] using
    Erdos357.erdos_357.variants.infinite_set_lower_density A hMono hd

/-- The same fully expanded hypothesis and the standard strict-cutoff natural formula. -/
example (A : ℕ → ℕ) (hMono : StrictMono A)
    (hDistinct : ∀ J K : Finset ℕ,
      (J : Set ℕ).OrdConnected → (K : Set ℕ).OrdConnected →
      (∑ x ∈ J, A x) = (∑ x ∈ K, A x) → J = K) :
    Filter.atTop.liminf (fun b : ℕ =>
      (((Set.range A ∩ Set.Iio b).ncard : ℝ) / (b : ℝ))) = 0 := by
  have hd : Erdos357.HasDistinctSums A := by
    intro J hJ K hK hs
    exact hDistinct J K hJ hK hs
  rw [← Set.lowerDensity_nat_eq_liminf]
  exact Erdos357.erdos_357.variants.infinite_set_lower_density A hMono hd

#print axioms Set.partialDensity
#print axioms Set.lowerDensity
#print axioms Set.partialDensity_nonneg
#print axioms Set.lowerDensity_nonneg
#print axioms Set.ncard_Iio_nat
#print axioms Set.partialDensity_nat_univ
#print axioms Set.lowerDensity_nat_eq_liminf
#print axioms Erdos357.HasDistinctSums
#print axioms Erdos357.blockSum
#print axioms Erdos357.blockSum_injective
#print axioms Erdos357.blockSum_le_of_linear_bound
#print axioms Erdos357.dyadicBlock
#print axioms Erdos357.dyadicBlock_card
#print axioms Erdos357.dyadicBlock_length_pos
#print axioms Erdos357.dyadicBlock_sum_lt
#print axioms Erdos357.dyadicBlock_disjoint
#print axioms Erdos357.no_linear_bound
#print axioms Erdos357.count_range_Iio_apply
#print axioms Erdos357.exists_linear_bound_of_lowerDensity_pos
#print axioms Erdos357.erdos_357.variants.infinite_set_lower_density
