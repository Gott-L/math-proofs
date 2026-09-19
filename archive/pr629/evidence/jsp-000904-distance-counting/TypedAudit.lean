import E1087

open Finset Erdos1087

example {α κ : Type*} [DecidableEq α] (P : Finset α) (c : Finset α → κ) :
    totalWeight P c = (disjointPairs P c).card +
      (P.card - 3) * (trianglePairs P c).card := totalWeight_identity P c

example (P : Finset Plane) (hP : 4 ≤ P.card) :
    8 * totalWeight P planeColor + 2 * P.card * (P.card - 1) =
      (planeQuadruples P).card + 8 * (P.card - 4) * (trianglePairs P planeColor).card :=
  planar_weighted_identity P hP

example (P : Finset Plane) :
    badCount P planeColor ≤ totalWeight P planeColor ∧
      totalWeight P planeColor ≤ 10 * badCount P planeColor := planar_comparison P

example {α κ : Type*} [DecidableEq α] (P : Finset α) (c : Finset α → κ)
    (q : Finset (Finset α)) :
    q ∈ equalPairs P c ↔ q ⊆ P.powersetCard 2 ∧ q.card = 2 ∧
      ∀ e ∈ q, ∀ f ∈ q, c e = c f := mem_equalPairs

example (P : Finset Plane) (q : (Plane × Plane) × (Plane × Plane)) :
    q ∈ planeQuadruples P ↔
      ((q.1.1 ∈ P ∧ q.1.2 ∈ P) ∧ (q.2.1 ∈ P ∧ q.2.2 ∈ P)) ∧
      Real.sqrt ((q.1.1.1-q.1.2.1)^2 + (q.1.1.2-q.1.2.2)^2) =
        Real.sqrt ((q.2.1.1-q.2.2.1)^2 + (q.2.1.2-q.2.2.2)^2) ∧
      0 < Real.sqrt ((q.1.1.1-q.1.2.1)^2 + (q.1.1.2-q.1.2.2)^2) := by
  classical
  simp [planeQuadruples, planeDistance, sqDist]

example (S : Finset Plane) (hS : S.card = 4) :
    0 < weight S planeColor ↔ ((edges S).image planeEdgeLength).card < 6 := by
  classical
  exact planar_degenerate_iff S hS

example : sharpSet.card = 4 ∧ badCount sharpSet planeColor = 1 ∧
    totalWeight sharpSet planeColor = 10 := planar_sharpness
