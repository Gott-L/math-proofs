/-
Copyright 2026. Released under the Apache 2.0 license.
Internal cross-module review by a separate Codex agent on the same team.
These explicit statements supplement, and do not replace, source review.
-/
import E1087

open Finset Classical Erdos1087
set_option maxHeartbeats 400000

namespace E1087InternalReview

section Generic
variable {α κ : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem edges_definition (P : Finset α) : edges P = P.powersetCard 2 := rfl

omit [DecidableEq α] in
theorem equalPairs_definition (P : Finset α) (c : Finset α → κ) :
    equalPairs P c = (by
      classical
      exact ((edges P).powersetCard 2).filter
        (fun q => ∀ e ∈ q, ∀ f ∈ q, c e = c f)) := rfl

theorem support_definition (q : Finset (Finset α)) :
    support q = q.biUnion id := rfl

theorem triangle_definition (P : Finset α) (c : Finset α → κ) :
    trianglePairs P c = (by
      classical
      exact (equalPairs P c).filter (fun q => (support q).card = 3)) := rfl

theorem disjoint_definition (P : Finset α) (c : Finset α → κ) :
    disjointPairs P c = (by
      classical
      exact (equalPairs P c).filter (fun q => (support q).card = 4)) := rfl

omit [DecidableEq α] in
theorem weight_definition (S : Finset α) (c : Finset α → κ) :
    weight S c = (equalPairs S c).card := rfl

omit [DecidableEq α] in
theorem totalWeight_definition (P : Finset α) (c : Finset α → κ) :
    totalWeight P c = ∑ S ∈ P.powersetCard 4, weight S c := rfl

theorem incidence_identity (P : Finset α) (c : Finset α → κ) :
    totalWeight P c = (disjointPairs P c).card +
      (P.card - 3) * (trianglePairs P c).card := totalWeight_identity P c

end Generic

theorem distance_definition (x y : Plane) :
    planeDistance x y = Real.sqrt ((x.1-y.1)^2 + (x.2-y.2)^2) := rfl

theorem unordered_edge_length {a b : Plane} (hab : a ≠ b) :
    planeEdgeLength {a,b} = Real.sqrt ((a.1-b.1)^2 + (a.2-b.2)^2) :=
  planeEdgeLength_pair hab

/-- The actual Q endpoint, with the ordered positive Euclidean-distance
predicate fully written out, allowing repeated points across the two edges. -/
theorem raw_quadruples_identity (P : Finset Plane) :
    (((P ×ˢ P) ×ˢ (P ×ˢ P)).filter (fun q =>
      Real.sqrt ((q.1.1.1-q.1.2.1)^2 + (q.1.1.2-q.1.2.2)^2) =
        Real.sqrt ((q.2.1.1-q.2.2.1)^2 + (q.2.1.2-q.2.2.2)^2) ∧
      0 < Real.sqrt ((q.1.1.1-q.1.2.1)^2 + (q.1.1.2-q.1.2.2)^2))).card =
      2 * P.card * (P.card-1) +
        8 * ((trianglePairs P planeColor).card + (disjointPairs P planeColor).card) := by
  simpa only [planeQuadruples, planeDistance, sqDist] using planar_quadruples_identity P

/-- F literally counts four-point subsets having fewer than six ordinary
Euclidean edge lengths, rather than merely an uninterpreted color predicate. -/
theorem raw_bad_count (P : Finset Plane) :
    badCount P planeColor =
      ((P.powersetCard 4).filter
        (fun S => ((S.powersetCard 2).image planeEdgeLength).card < 6)).card := by
  unfold badCount badFourSets
  congr 1
  apply filter_congr
  intro S hS
  exact planar_degenerate_iff S (mem_powersetCard.mp hS).2

theorem raw_planar_comparison (P : Finset Plane) :
    ((P.powersetCard 4).filter
      (fun S => ((S.powersetCard 2).image planeEdgeLength).card < 6)).card ≤
        ∑ S ∈ P.powersetCard 4, (equalPairs S planeColor).card ∧
    (∑ S ∈ P.powersetCard 4, (equalPairs S planeColor).card) ≤
      10 * ((P.powersetCard 4).filter
        (fun S => ((S.powersetCard 2).image planeEdgeLength).card < 6)).card := by
  rw [← raw_bad_count]
  exact planar_comparison P

theorem weighted_identity (P : Finset Plane) (hP : 4 ≤ P.card) :
    8 * (∑ S ∈ P.powersetCard 4, (equalPairs S planeColor).card) +
        2 * P.card * (P.card-1) =
      (planeQuadruples P).card +
        8 * (P.card-4) * (trianglePairs P planeColor).card :=
  planar_weighted_identity P hP

theorem exact_sharpness : sharpSet.card = 4 ∧
    ((sharpSet.powersetCard 4).filter
      (fun S => ((S.powersetCard 2).image planeEdgeLength).card < 6)).card = 1 ∧
    (∑ S ∈ sharpSet.powersetCard 4, (equalPairs S planeColor).card) = 10 := by
  rw [← raw_bad_count]
  exact planar_sharpness

end E1087InternalReview
