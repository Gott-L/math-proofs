/-
Copyright 2026. Released under the Apache 2.0 license.
Project initiation, direction and submission ownership: Gott-L.
Formal implementation: Codex assistance.

Independent Lean formalization of the planar multiplicity argument and
sharpness example in haipapa123's JSP-000904 PR 586, fixed commit
daa68321eca18b869069e5cdec51ab5526d57558. Its source exposition is CC BY 4.0.
-/
import E1087ColorBound
import Mathlib.Data.Real.Sqrt

open Finset

namespace Erdos1087

abbrev Plane := ℝ × ℝ

def sqDist (x y : Plane) : ℝ := (x.1 - y.1)^2 + (x.2 - y.2)^2

noncomputable def planeColor (e : Finset Plane) : ℝ :=
  ∑ x ∈ e, ∑ y ∈ e, sqDist x y

@[simp] theorem sqDist_self (x : Plane) : sqDist x x = 0 := by
  simp [sqDist]

theorem sqDist_comm (x y : Plane) : sqDist x y = sqDist y x := by
  unfold sqDist
  ring

theorem sqDist_pos {x y : Plane} (h : x ≠ y) : 0 < sqDist x y := by
  unfold sqDist
  have hx := sq_nonneg (x.1 - y.1)
  have hy := sq_nonneg (x.2 - y.2)
  by_contra hn
  have h1 : x.1 = y.1 := by nlinarith
  have h2 : x.2 = y.2 := by nlinarith
  exact h (Prod.ext h1 h2)

theorem planeColor_pair {x y : Plane} (hxy : x ≠ y) :
    planeColor {x,y} = 2 * sqDist x y := by
  classical
  simp [planeColor, hxy, Ne.symm hxy, sqDist_comm y x]
  ring

set_option maxHeartbeats 1600000 in
/-- Four distinct planar points cannot have all six distances equal. -/
theorem no_four_equidistant (a b c d : Plane) (hab : a ≠ b)
    (hac : sqDist a c = sqDist a b)
    (had : sqDist a d = sqDist a b)
    (hbc : sqDist b c = sqDist a b)
    (hbd : sqDist b d = sqDist a b)
    (hcd : sqDist c d = sqDist a b) : False := by
  let ux := b.1 - a.1
  let uy := b.2 - a.2
  let vx := c.1 - a.1
  let vy := c.2 - a.2
  let wx := d.1 - a.1
  let wy := d.2 - a.2
  let ρ := sqDist a b
  have hρ : 0 < ρ := sqDist_pos hab
  have hu : ux^2 + uy^2 = ρ := by dsimp [ux,uy,ρ,sqDist]; ring
  have hv : vx^2 + vy^2 = ρ := by
    dsimp [vx,vy,ρ,sqDist]
    dsimp [sqDist] at hac
    nlinarith only [hac]
  have hw : wx^2 + wy^2 = ρ := by
    dsimp [wx,wy,ρ,sqDist]
    dsimp [sqDist] at had
    nlinarith only [had]
  have huv : ux*vx + uy*vy = ρ/2 := by
    dsimp [ux,uy,vx,vy,ρ,sqDist]
    dsimp [sqDist] at hac hbc
    nlinarith only [hac, hbc]
  have huw : ux*wx + uy*wy = ρ/2 := by
    dsimp [ux,uy,wx,wy,ρ,sqDist]
    dsimp [sqDist] at had hbd
    nlinarith only [had, hbd]
  have hvw : vx*wx + vy*wy = ρ/2 := by
    dsimp [vx,vy,wx,wy,ρ,sqDist]
    dsimp [sqDist] at hac had hcd
    nlinarith only [hac, had, hcd]
  have hGram :
      (ux^2+uy^2)*(vx^2+vy^2)*(wx^2+wy^2) +
      2*(ux*vx+uy*vy)*(ux*wx+uy*wy)*(vx*wx+vy*wy) -
      (ux^2+uy^2)*(vx*wx+vy*wy)^2 -
      (vx^2+vy^2)*(ux*wx+uy*wy)^2 -
      (wx^2+wy^2)*(ux*vx+uy*vy)^2 = 0 := by ring
  rw [hu, hv, hw, huv, huw, hvw] at hGram
  nlinarith only [hGram, pow_pos hρ 3]

theorem four_set_has_different_edge_colors (S : Finset Plane) (hS : S.card = 4) :
    ∃ e ∈ edges S, ∃ f ∈ edges S, planeColor e ≠ planeColor f := by
  classical
  by_contra hnot
  push_neg at hnot
  obtain ⟨a, ha⟩ := card_pos.mp (show 0 < S.card by omega)
  have hthree : (S.erase a).card = 3 := by rw [card_erase_of_mem ha, hS]
  obtain ⟨b,c,d,hbc,hbd,hcd,hT⟩ := card_eq_three.mp hthree
  have hb : b ∈ S.erase a := by rw [hT]; simp
  have hc : c ∈ S.erase a := by rw [hT]; simp
  have hd : d ∈ S.erase a := by rw [hT]; simp
  have hab : a ≠ b := (ne_of_mem_erase hb).symm
  have hac : a ≠ c := (ne_of_mem_erase hc).symm
  have had : a ≠ d := (ne_of_mem_erase hd).symm
  have hpair {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
      ({x,y} : Finset Plane) ∈ edges S := by
    apply mem_edges.mpr
    constructor
    · intro z hz
      simp only [mem_insert, mem_singleton] at hz
      rcases hz with rfl | rfl <;> assumption
    · simp [hne]
  have hdist {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y) :
      sqDist x y = sqDist a b := by
    have h := hnot {x,y} (hpair hx hy hne) {a,b} (hpair ha (mem_of_mem_erase hb) hab)
    rw [planeColor_pair hne, planeColor_pair hab] at h
    linarith
  exact no_four_equidistant a b c d hab
    (hdist ha (mem_of_mem_erase hc) hac)
    (hdist ha (mem_of_mem_erase hd) had)
    (hdist (mem_of_mem_erase hb) (mem_of_mem_erase hc) hbc)
    (hdist (mem_of_mem_erase hb) (mem_of_mem_erase hd) hbd)
    (hdist (mem_of_mem_erase hc) (mem_of_mem_erase hd) hcd)

theorem weight_plane_le_ten (S : Finset Plane) (hS : S.card = 4) :
    weight S planeColor ≤ 10 := by
  classical
  apply monochromatic_pairs_le_ten (edges S) planeColor
  · simp only [edges, card_powersetCard, hS]
    decide
  · exact four_set_has_different_edge_colors S hS



noncomputable def sharpP0 : Plane := (0,0)
noncomputable def sharpP1 : Plane := (2,0)
noncomputable def sharpP2 : Plane := (3,Real.sqrt 3)
noncomputable def sharpP3 : Plane := (1,Real.sqrt 3)

noncomputable def sharpSet : Finset Plane := by
  classical
  exact {sharpP0, sharpP1, sharpP2, sharpP3}

noncomputable def shortEdges : Finset (Finset Plane) := by
  classical
  exact {{sharpP0,sharpP1}, {sharpP0,sharpP3}, {sharpP1,sharpP2},
    {sharpP1,sharpP3}, {sharpP2,sharpP3}}

theorem sharpSet_card : sharpSet.card = 4 := by
  classical
  norm_num [sharpSet, sharpP0, sharpP1, sharpP2, sharpP3, Prod.ext_iff]

theorem shortEdges_card : shortEdges.card = 5 := by
  classical
  have hneq : ∀ a b c d : Plane, a ≠ b → a ≠ c → a ≠ d →
      ({a,b} : Finset Plane) ≠ {c,d} := by
    intro a b c d _ hac had h
    have hm : a ∈ ({c,d} : Finset Plane) := by rw [← h]; simp
    simp [hac, had] at hm
  have hmem : ∀ x : Plane, x ∈ ({sharpP0,sharpP1} : Finset Plane) ↔
      x = sharpP0 ∨ x = sharpP1 := by simp
  have h01_03 : ({sharpP0,sharpP1} : Finset Plane) ≠ {sharpP0,sharpP3} := by
    intro h
    have hm : sharpP1 ∈ ({sharpP0,sharpP3} : Finset Plane) := by rw [←h]; simp
    norm_num [sharpP0,sharpP1,sharpP3,Prod.ext_iff] at hm
  have h01_12 : ({sharpP0,sharpP1} : Finset Plane) ≠ {sharpP1,sharpP2} := by
    apply hneq <;> norm_num [sharpP0,sharpP1,sharpP2,Prod.ext_iff]
  have h01_13 : ({sharpP0,sharpP1} : Finset Plane) ≠ {sharpP1,sharpP3} := by
    apply hneq <;> norm_num [sharpP0,sharpP1,sharpP3,Prod.ext_iff]
  have h01_23 : ({sharpP0,sharpP1} : Finset Plane) ≠ {sharpP2,sharpP3} := by
    apply hneq <;> norm_num [sharpP0,sharpP1,sharpP2,sharpP3,Prod.ext_iff]
  have h03_12 : ({sharpP0,sharpP3} : Finset Plane) ≠ {sharpP1,sharpP2} := by
    apply hneq <;> norm_num [sharpP0,sharpP1,sharpP2,sharpP3,Prod.ext_iff]
  have h03_13 : ({sharpP0,sharpP3} : Finset Plane) ≠ {sharpP1,sharpP3} := by
    apply hneq <;> norm_num [sharpP0,sharpP1,sharpP3,Prod.ext_iff]
  have h03_23 : ({sharpP0,sharpP3} : Finset Plane) ≠ {sharpP2,sharpP3} := by
    apply hneq <;> norm_num [sharpP0,sharpP2,sharpP3,Prod.ext_iff]
  have h12_13 : ({sharpP1,sharpP2} : Finset Plane) ≠ {sharpP1,sharpP3} := by
    intro h
    have hm : sharpP2 ∈ ({sharpP1,sharpP3} : Finset Plane) := by rw [←h]; simp
    norm_num [sharpP1,sharpP2,sharpP3,Prod.ext_iff] at hm
  have h12_23 : ({sharpP1,sharpP2} : Finset Plane) ≠ {sharpP2,sharpP3} := by
    apply hneq <;> norm_num [sharpP1,sharpP2,sharpP3,Prod.ext_iff]
  have h13_23 : ({sharpP1,sharpP3} : Finset Plane) ≠ {sharpP2,sharpP3} := by
    apply hneq <;> norm_num [sharpP1,sharpP2,sharpP3,Prod.ext_iff]
  simp [shortEdges, h01_03,h01_12,h01_13,h01_23,h03_12,h03_13,h03_23,h12_13,h12_23,h13_23]

theorem shortEdges_subset : shortEdges ⊆ edges sharpSet := by
  classical
  intro e he
  simp only [shortEdges, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  all_goals
    apply mem_edges.mpr
    constructor
    · intro x hx
      simp only [mem_insert, mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp [sharpSet]
    · norm_num [sharpP0,sharpP1,sharpP2,sharpP3,Prod.ext_iff]

theorem shortEdges_color {e : Finset Plane} (he : e ∈ shortEdges) :
    planeColor e = 8 := by
  classical
  simp only [shortEdges, mem_insert, mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num [planeColor, sqDist, sharpP0,sharpP1,sharpP2,sharpP3,Prod.ext_iff]

theorem sharpSet_weight : weight sharpSet planeColor = 10 := by
  classical
  apply le_antisymm (weight_plane_le_ten sharpSet sharpSet_card)
  have hsub : shortEdges.powersetCard 2 ⊆ equalPairs sharpSet planeColor := by
    intro q hq
    obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp hq
    apply mem_equalPairs.mpr
    refine ⟨fun e he => shortEdges_subset (hsub he), hcard, ?_⟩
    intro e he f hf
    rw [shortEdges_color (hsub he), shortEdges_color (hsub hf)]
  have h := card_le_card hsub
  rw [card_powersetCard, shortEdges_card] at h
  exact h

theorem sharpSet_badCount : badCount sharpSet planeColor = 1 := by
  classical
  rw [badCount, badFourSets, ← sharpSet_card, powersetCard_self]
  have hp : 0 < weight sharpSet planeColor := by rw [sharpSet_weight]; decide
  have heq : ({sharpSet} : Finset (Finset Plane)).filter
      (fun S => 0 < weight S planeColor) = {sharpSet} := by
    ext S
    simp only [mem_filter, mem_singleton]
    exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hp⟩⟩
  rw [heq]
  exact card_singleton _


end Erdos1087
