/-
Copyright 2026. Released under the Apache 2.0 license.
Project initiation, direction and submission ownership: Gott-L.
Formal proof development and implementation: Codex assistance.

Formalizes the exact finite counting identities and planar comparison in
haipapa123's JSP-000904 note, commit daa68321eca18b869069e5cdec51ab5526d57558.
The mathematical source is credited under CC BY 4.0. These results do not
assert the open asymptotic conclusion of Erdős Problem 1087.
-/
import E1087Incidence
import E1087Meaning
import E1087Quadruples
import E1087Plane

open Finset

namespace Erdos1087

/-- The ordinary Euclidean distance on the coordinate plane. -/
noncomputable def planeDistance (x y : Plane) : ℝ := Real.sqrt (sqDist x y)

theorem sqDist_nonneg (x y : Plane) : 0 ≤ sqDist x y :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem planeDistance_pos_iff (x y : Plane) : 0 < planeDistance x y ↔ x ≠ y := by
  rw [planeDistance, Real.sqrt_pos]
  constructor
  · intro h hxy
    subst y
    simp at h
  · exact sqDist_pos

theorem planeDistance_eq_iff (a b c d : Plane) :
    planeDistance a b = planeDistance c d ↔ sqDist a b = sqDist c d :=
  Real.sqrt_inj (sqDist_nonneg a b) (sqDist_nonneg c d)

/-- Euclidean length of an unordered edge, independent of an orientation. -/
noncomputable def planeEdgeLength (e : Finset Plane) : ℝ :=
  Real.sqrt (planeColor e / 2)

theorem planeEdgeLength_pair {a b : Plane} (hab : a ≠ b) :
    planeEdgeLength {a,b} = planeDistance a b := by
  rw [planeEdgeLength, planeColor_pair hab]
  simp [planeDistance]

theorem planeColor_nonneg (e : Finset Plane) : 0 ≤ planeColor e := by
  unfold planeColor
  exact sum_nonneg (fun _ _ => sum_nonneg (fun _ _ => sqDist_nonneg _ _))

theorem edge_length_color_card (S : Finset Plane) :
    ((edges S).image planeEdgeLength).card = ((edges S).image planeColor).card := by
  classical
  have heq : (edges S).image planeEdgeLength =
      ((edges S).image planeColor).image (fun t : ℝ => Real.sqrt (t / 2)) := by
    rw [image_image]
    rfl
  rw [heq]
  apply card_image_of_injOn
  intro x hx y hy hxy
  obtain ⟨e, _, rfl⟩ := mem_image.mp hx
  obtain ⟨f, _, rfl⟩ := mem_image.mp hy
  have he := planeColor_nonneg e
  have hf := planeColor_nonneg f
  have h := (Real.sqrt_inj (div_nonneg he (by norm_num))
    (div_nonneg hf (by norm_num))).mp hxy
  linarith

theorem planar_degenerate_iff (S : Finset Plane) (hS : S.card = 4) :
    0 < weight S planeColor ↔ ((edges S).image planeEdgeLength).card < 6 := by
  classical
  rw [edge_length_color_card]
  exact four_set_degenerate_iff S planeColor hS

/-- Actual ordered distance quadruples. Only each edge must be nondegenerate;
the two edges can coincide or share endpoints. -/
noncomputable def planeQuadruples (P : Finset Plane) :
    Finset ((Plane × Plane) × (Plane × Plane)) := by
  classical
  exact ((P ×ˢ P) ×ˢ (P ×ˢ P)).filter (fun q =>
    planeDistance q.1.1 q.1.2 = planeDistance q.2.1 q.2.2 ∧
      0 < planeDistance q.1.1 q.1.2)

theorem planeQuadruples_eq (P : Finset Plane) :
    planeQuadruples P = orderedQuadruples P (fun x y => 2 * sqDist x y) := by
  classical
  ext q
  simp only [planeQuadruples, orderedQuadruples, mem_filter]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨heq, hpos⟩
    have hother : 0 < planeDistance q.2.1 q.2.2 := heq ▸ hpos
    exact ⟨(planeDistance_pos_iff _ _).mp hpos,
      (planeDistance_pos_iff _ _).mp hother,
      congrArg (fun t : ℝ => 2 * t) ((planeDistance_eq_iff _ _ _ _).mp heq)⟩
  · rintro ⟨h1, _, heq⟩
    exact ⟨(planeDistance_eq_iff _ _ _ _).mpr (by linarith),
      (planeDistance_pos_iff _ _).mpr h1⟩

theorem two_mul_edges_card {α : Type*} (P : Finset α) :
    2 * (edges P).card = P.card * (P.card - 1) := by
  rw [edges, card_powersetCard]
  generalize P.card = n
  cases n with
  | zero => simp
  | succ n =>
    simpa [Nat.choose_one_right, Nat.mul_comm] using
      (Nat.succ_mul_choose_eq n 1).symm

/-- The factors four and eight come from proved orientation fibers. -/
theorem planar_quadruples_identity (P : Finset Plane) :
    (planeQuadruples P).card = 2 * P.card * (P.card - 1) +
      8 * ((trianglePairs P planeColor).card + (disjointPairs P planeColor).card) := by
  classical
  rw [planeQuadruples_eq, orderedQuadruples_card P (fun x y => 2 * sqDist x y)
      planeColor (fun _ _ h => planeColor_pair h), equalPairs_card_partition]
  have h := two_mul_edges_card P
  nlinarith

/-- Exact weighted identity for every finite planar set with at least four points. -/
theorem planar_weighted_identity (P : Finset Plane) (hP : 4 ≤ P.card) :
    8 * totalWeight P planeColor + 2 * P.card * (P.card - 1) =
      (planeQuadruples P).card + 8 * (P.card - 4) * (trianglePairs P planeColor).card := by
  rw [totalWeight_identity, planar_quadruples_identity]
  have h : P.card - 3 = P.card - 4 + 1 := by omega
  rw [h]
  ring

/-- The universal comparison with the actual number of bad four-point sets. -/
theorem planar_comparison (P : Finset Plane) :
    badCount P planeColor ≤ totalWeight P planeColor ∧
      totalWeight P planeColor ≤ 10 * badCount P planeColor := by
  classical
  exact ⟨badCount_le_totalWeight P planeColor,
    totalWeight_le_mul_badCount P planeColor 10
      (fun S hS => weight_plane_le_ten S (mem_powersetCard.mp hS).2)⟩

/-- The comparison factor ten is attained by a four-point planar set. -/
theorem planar_sharpness : sharpSet.card = 4 ∧
    badCount sharpSet planeColor = 1 ∧ totalWeight sharpSet planeColor = 10 := by
  classical
  refine ⟨sharpSet_card, sharpSet_badCount, ?_⟩
  rw [totalWeight, ← sharpSet_card, powersetCard_self]
  simpa using sharpSet_weight

end Erdos1087
