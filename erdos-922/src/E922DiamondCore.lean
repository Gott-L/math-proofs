/-
Inherited Folkman/Erdos922 proof, original lines 1983--2534.
plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos922.lean, SHA256
0bc22004ecbe76ab3cc3f263c29c76994b39017828ea835d987139fa324b9971.
Original informal author: Jon Folkman. Formal authors: Codex; GPT-5.6 Sol.
Local Lean4.19 port under Gott-L's direction, with Codex/B implementation.
Private experiment; upstream license not verified. No mathematical novelty claim.
-/
import E922StructureEvenHole

open SimpleGraph
open scoped ENat


open SimpleGraph

namespace Erdos922Diamond

universe u v

section MissingColor

variable {V : Type u} {G : SimpleGraph V} {x y : V}

/-- Folkman's missing-color recoloring.  The values of `c` at `x,y` are
irrelevant: the validation theorem asks only that it properly colors the
remaining vertices. -/
noncomputable def missingColorRecolor {α : Type v}
    [DecidableEq V] [DecidableEq α] [DecidableRel G.Adj]
    (c : V → α) (i : α) : V → Option α :=
  fun z ↦
    if z = y then none
    else if z = x then some i
    else if G.Adj x z ∧ c z = i then none
    else some (c z)

theorem missingColorRecolor_valid {α : Type v}
    [DecidableEq V] [DecidableEq α] [DecidableRel G.Adj]
    (hxy : G.Adj x y) (c : V → α) (i : α)
    (hc : ∀ ⦃a b⦄, G.Adj a b → a ≠ x → a ≠ y → b ≠ x → b ≠ y → c a ≠ c b)
    (hmiss : ∀ z, G.Adj x z → G.Adj y z → c z ≠ i) :
    ∀ ⦃a b⦄, G.Adj a b →
      missingColorRecolor (G := G) (x := x) (y := y) c i a ≠
        missingColorRecolor (G := G) (x := x) (y := y) c i b := by
  classical
  intro a b hab
  have habne : a ≠ b := hab.ne
  by_cases haY : a = y
  · subst a
    have hbY : b ≠ y := habne.symm
    by_cases hbX : b = x
    · subst b
      simp [missingColorRecolor, hxy.ne]
    · by_cases hbR : G.Adj x b ∧ c b = i
      · exact (hmiss b hbR.1 hab hbR.2).elim
      · simp [missingColorRecolor, hbY, hbX, hbR]
  · by_cases hbY : b = y
    · subst b
      by_cases haX : a = x
      · subst a
        simp [missingColorRecolor, hxy.ne]
      · by_cases haR : G.Adj x a ∧ c a = i
        · exact (hmiss a haR.1 hab.symm haR.2).elim
        · simp [missingColorRecolor, haY, haX, haR]
    · by_cases haX : a = x
      · subst a
        have hbX : b ≠ x := habne.symm
        by_cases hbR : G.Adj x b ∧ c b = i
        · simp [missingColorRecolor, haY, hbY, hbX, hbR]
        · have hci : c b ≠ i := fun h ↦ hbR ⟨hab, h⟩
          simp [missingColorRecolor, haY, hbY, hbX, hci, hci.symm]
      · by_cases hbX : b = x
        · subst b
          by_cases haR : G.Adj x a ∧ c a = i
          · simp [missingColorRecolor, haY, haX, hbY, haR]
          · have hci : c a ≠ i := fun h ↦ haR ⟨hab.symm, h⟩
            simp [missingColorRecolor, haY, haX, hbY, hci]
        · have hcAB : c a ≠ c b := hc hab haX haY hbX hbY
          by_cases haR : G.Adj x a ∧ c a = i <;>
            by_cases hbR : G.Adj x b ∧ c b = i
          · exact (hcAB (haR.2.trans hbR.2.symm)).elim
          · simp [missingColorRecolor, haY, haX, hbY, hbX, haR, hbR]
          · simp [missingColorRecolor, haY, haX, hbY, hbX, haR, hbR]
          · simpa [missingColorRecolor, haY, haX, hbY, hbX, haR, hbR] using hcAB

noncomputable def coloringOptionOfMissingCommonColor {α : Type v}
    [DecidableEq V] [DecidableEq α] [DecidableRel G.Adj]
    (hxy : G.Adj x y) (c : V → α) (i : α)
    (hc : ∀ ⦃a b⦄, G.Adj a b → a ≠ x → a ≠ y → b ≠ x → b ≠ y → c a ≠ c b)
    (hmiss : ∀ z, G.Adj x z → G.Adj y z → c z ≠ i) :
    G.Coloring (Option α) :=
  Coloring.mk (missingColorRecolor (G := G) (x := x) (y := y) c i)
    (fun {_ _} h ↦
      missingColorRecolor_valid (G := G) (x := x) (y := y) hxy c i hc hmiss h)

end MissingColor

section PairIdentification

variable {V : Type u} (x y : V)

/-- The vertices left after deleting the adjacent pair `x,y`. -/
abbrev DeletedPair := ({x, y}ᶜ : Set V)

/-- The vertex type after deleting `x,y` and using `u` as the representative
of the identified pair `u,v`. -/
abbrev IdentifiedPair (v : V) := {z : DeletedPair x y // z.1 ≠ v}

/-- Identify `v` with `u`, retaining `u` as the representative. -/
noncomputable def pairIdentify (u v : V) (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v) :
    DeletedPair x y → IdentifiedPair x y v := by
  classical
  exact fun z ↦ if hz : z.1 = v then
      ⟨⟨u, by simp [hux, huy]⟩, huv⟩
    else ⟨z, hz⟩

variable {x y : V} {G : SimpleGraph V} {u v : V}

/-- The graph obtained from `G - {x,y}` by identifying the nonadjacent
vertices `u,v`. -/
noncomputable def pairGraph (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v) :
    SimpleGraph (IdentifiedPair x y v) :=
  (G.induce ({x, y}ᶜ : Set V)).mapFunctionCompat (pairIdentify x y u v hux huy huv)

theorem pairIdentify_ne_of_adj
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v) {a b : DeletedPair x y}
    (hab : (G.induce ({x, y}ᶜ : Set V)).Adj a b) :
    pairIdentify x y u v hux huy huv a ≠
      pairIdentify x y u v hux huy huv b := by
  intro heq
  have heqv := congrArg (fun z : IdentifiedPair x y v ↦ z.1.1) heq
  by_cases ha : a.1 = v <;> by_cases hb : b.1 = v
  · exact hab.ne (Subtype.ext (ha.trans hb.symm))
  · simp only [pairIdentify, dif_pos ha, dif_neg hb] at heqv
    have hbu : b.1 = u := heqv.symm
    exact huvNA (by simpa [ha, hbu] using hab.symm)
  · simp only [pairIdentify, dif_neg ha, dif_pos hb] at heqv
    have hau : a.1 = u := heqv
    exact huvNA (by simpa [hau, hb] using hab)
  · simp only [pairIdentify, dif_neg ha, dif_neg hb] at heqv
    have habv : a.1 = b.1 := heqv
    exact hab.ne (Subtype.ext habv)

/-- Pull a coloring of the pair-identification graph back to a coloring of
`G - {x,y}`. -/
noncomputable def pairGraphPullColoring {α : Type v}
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v)
    (C : (pairGraph (G := G) hux huy huv).Coloring α) :
    (G.induce ({x, y}ᶜ : Set V)).Coloring α := by
  refine Coloring.mk (fun z ↦ C (pairIdentify x y u v hux huy huv z)) ?_
  intro a b hab
  exact C.valid (SimpleGraph.mapFunctionCompat_adj_apply hab
    (pairIdentify_ne_of_adj hux huy huv huvNA hab))

/-- Extend the pulled-back coloring arbitrarily to `x,y`; these two values
are ignored by `missingColorRecolor_valid`. -/
noncomputable def pairGraphPullFunction {α : Type v}
    [DecidableEq V]
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v)
    (C : (pairGraph (G := G) hux huy huv).Coloring α) (fallback : α) : V → α :=
  fun z ↦ if hz : z ∈ ({x, y}ᶜ : Set V) then
    pairGraphPullColoring hux huy huv huvNA C ⟨z, hz⟩
  else fallback

theorem pairGraphPullFunction_valid {α : Type v}
    [DecidableEq V]
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v)
    (C : (pairGraph (G := G) hux huy huv).Coloring α) (fallback : α) :
    ∀ ⦃a b⦄, G.Adj a b → a ≠ x → a ≠ y → b ≠ x → b ≠ y →
      pairGraphPullFunction hux huy huv huvNA C fallback a ≠
        pairGraphPullFunction hux huy huv huvNA C fallback b := by
  intro a b hab hax hay hbx hby
  have hab' : (G.induce ({x, y}ᶜ : Set V)).Adj
      ⟨a, by simp [hax, hay]⟩ ⟨b, by simp [hbx, hby]⟩ := hab
  simpa [pairGraphPullFunction, hax, hay, hbx, hby] using
    (pairGraphPullColoring hux huy huv huvNA C).valid hab'

/-- A coloring in which `u,v` have the same color descends to the graph that
identifies them. -/
noncomputable def pairGraphColoringOfEqual {α : Type v}
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
    (huv : u ≠ v)
    (c : (G.induce ({x, y}ᶜ : Set V)).Coloring α)
    (heq : c ⟨u, by simp [hux, huy]⟩ = c ⟨v, by simp [hvx, hvy]⟩) :
    (pairGraph (G := G) hux huy huv).Coloring α := by
  classical
  let f := pairIdentify x y u v hux huy huv
  refine Coloring.mk (fun z ↦ c z.1) ?_
  intro a b hab
  rcases hab with
    ⟨-, a', b', hab', ha', hb'⟩
  have color_identify : ∀ z : DeletedPair x y, c z = c (f z).1 := by
    intro z
    by_cases hz : z.1 = v
    · have hzsub : z = ⟨v, by simp [hvx, hvy]⟩ := Subtype.ext hz
      subst z
      simpa [f, pairIdentify] using heq.symm
    · simp [f, pairIdentify, hz]
  rw [← ha', ← hb']
  exact fun h ↦ c.valid hab'
    ((color_identify a').trans (h.trans (color_identify b').symm))

/-- Pulling back a descended coloring recovers the original coloring, provided
the identified vertices had equal colors. -/
theorem pairGraph_roundTrip {α : Type v}
    [DecidableEq V]
    (hux : u ≠ x) (huy : u ≠ y) (hvx : v ≠ x) (hvy : v ≠ y)
    (huv : u ≠ v) (huvNA : ¬ G.Adj u v)
    (c : (G.induce ({x, y}ᶜ : Set V)).Coloring α)
    (heq : c ⟨u, by simp [hux, huy]⟩ = c ⟨v, by simp [hvx, hvy]⟩)
    (fallback : α) (z : V) (hzx : z ≠ x) (hzy : z ≠ y) :
    pairGraphPullFunction hux huy huv huvNA
      (pairGraphColoringOfEqual hux huy hvx hvy huv c heq) fallback z =
      c ⟨z, by simp [hzx, hzy]⟩ := by
  classical
  simp only [pairGraphPullFunction, Set.mem_compl_iff, Set.mem_insert_iff,
    Set.mem_singleton_iff, not_or, hzx, hzy, and_self]
  change c (pairIdentify x y u v hux huy huv ⟨z, by simp [hzx, hzy]⟩).1 =
    c ⟨z, by simp [hzx, hzy]⟩
  by_cases hzv : z = v
  · subst z
    simpa [pairIdentify] using heq
  · simp [pairIdentify, hzv]

/-- C1.2 of the diamond argument: if `G` cannot be colored with one fresh
color beyond `α`, then every color of a coloring of the pair-identification
graph occurs on the image of a common neighbor of `x,y`. -/
theorem everyColorOccursOnIdentifiedCommonNeighbors {α : Type v}
    [DecidableEq V]
    (hxy : G.Adj x y)
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v)
    (hncol : ¬ Nonempty (G.Coloring (Option α)))
    (C : (pairGraph (G := G) hux huy huv).Coloring α) (i : α) :
    ∃ z, G.Adj x z ∧ G.Adj y z ∧
      pairGraphPullFunction hux huy huv huvNA C i z = i := by
  classical
  by_contra! hmiss
  apply hncol
  exact ⟨coloringOptionOfMissingCommonColor hxy
    (pairGraphPullFunction hux huy huv huvNA C i) i
    (pairGraphPullFunction_valid hux huy huv huvNA C i) hmiss⟩

end PairIdentification

section Apex

variable {V : Type u} {G : SimpleGraph V} {x y : V}

/-- `G - {x,y}` with a new apex adjacent precisely to common neighbors of
`x,y`; `none` is the apex and `some z` is an old vertex. -/
def commonNeighborApexGraph : SimpleGraph (Option (DeletedPair x y)) where
  Adj a b := match a, b with
    | none, none => False
    | none, some z => G.Adj x z.1 ∧ G.Adj y z.1
    | some z, none => G.Adj x z.1 ∧ G.Adj y z.1
    | some a, some b => G.Adj a.1 b.1
  symm := by
    intro a b h
    cases a with
    | none =>
        cases b with
        | none => exact h
        | some b => exact h
    | some a =>
        cases b with
        | none => exact h
        | some b => exact h.symm
  loopless := by
    intro a h
    cases a with
    | none => exact h
    | some a => exact h.ne rfl

@[simp] theorem commonNeighborApexGraph_adj_apex {z : DeletedPair x y} :
    (commonNeighborApexGraph (G := G)).Adj none (some z) ↔
      G.Adj x z.1 ∧ G.Adj y z.1 := Iff.rfl

@[simp] theorem commonNeighborApexGraph_adj_old {a b : DeletedPair x y} :
    (commonNeighborApexGraph (G := G)).Adj (some a) (some b) ↔
      G.Adj a.1 b.1 := Iff.rfl

/-- Restriction of an apex-graph coloring to the old vertices. -/
noncomputable def apexOldColoring {α : Type v}
    (C : (commonNeighborApexGraph (G := G) (x := x) (y := y)).Coloring α) :
    (G.induce ({x, y}ᶜ : Set V)).Coloring α := by
  refine Coloring.mk (fun z ↦ C (some z)) ?_
  intro a b hab
  exact C.valid hab

/-- The apex color is absent on all common neighbors. -/
theorem apexColor_missing_on_commonNeighbors {α : Type v}
    (C : (commonNeighborApexGraph (G := G) (x := x) (y := y)).Coloring α)
    (z : DeletedPair x y) (hzx : G.Adj x z.1) (hzy : G.Adj y z.1) :
    C (some z) ≠ C none :=
  C.valid ⟨hzx, hzy⟩

/-- Common neighbors, packaged as a finite type for pigeonhole arguments. -/
abbrev CommonNeighbor (G : SimpleGraph V) (x y : V) :=
  {z : V // G.Adj x z ∧ G.Adj y z}

/-- A common neighbor is an old vertex of the apex graph. -/
def CommonNeighbor.toDeletedPair (z : CommonNeighbor G x y) : DeletedPair x y :=
  ⟨z.1, by simp [z.2.1.ne.symm, z.2.2.ne.symm]⟩

/-- If there are more common neighbors than colors, an apex coloring has two
distinct, nonadjacent common neighbors with the same color. -/
theorem exists_nonadjacent_commonNeighbors_sameColor
    [Finite V] [Fintype α]
    (C : (commonNeighborApexGraph (G := G) (x := x) (y := y)).Coloring α)
    (hcard : Fintype.card α < Nat.card (CommonNeighbor G x y)) :
    ∃ u v : CommonNeighbor G x y, u.1 ≠ v.1 ∧ ¬ G.Adj u.1 v.1 ∧
      C (some u.toDeletedPair) = C (some v.toDeletedPair) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype (CommonNeighbor G x y) := Fintype.ofFinite _
  let color : CommonNeighbor G x y → α := fun z ↦ C (some z.toDeletedPair)
  have hcard' : Fintype.card α < Fintype.card (CommonNeighbor G x y) := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  obtain ⟨u, v, huv, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt color hcard'
  have huvVal : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  refine ⟨u, v, huvVal, ?_, heq⟩
  intro hadj
  exact C.valid (v := some u.toDeletedPair) (w := some v.toDeletedPair) hadj heq

/-- The apex graph is not `α`-colorable once the common-neighbor set is
larger than `α`.  This is the complete pigeonhole + pair-identification +
missing-color portion of Folkman's diamond argument. -/
theorem commonNeighborApexGraph_not_colorable
    [Finite V] [Fintype α]
    (hxy : G.Adj x y)
    (hncol : ¬ Nonempty (G.Coloring (Option α)))
    (hcard : Fintype.card α < Nat.card (CommonNeighbor G x y)) :
    ¬ Nonempty
      ((commonNeighborApexGraph (G := G) (x := x) (y := y)).Coloring α) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rintro ⟨C0⟩
  obtain ⟨u, v, huv, huvNA, heq⟩ :=
    exists_nonadjacent_commonNeighbors_sameColor C0 hcard
  have hux : u.1 ≠ x := u.2.1.ne.symm
  have huy : u.1 ≠ y := u.2.2.ne.symm
  have hvx : v.1 ≠ x := v.2.1.ne.symm
  have hvy : v.1 ≠ y := v.2.2.ne.symm
  let c := apexOldColoring C0
  have heq' : c ⟨u.1, by simp [hux, huy]⟩ =
      c ⟨v.1, by simp [hvx, hvy]⟩ := by
    change C0 (some ⟨u.1, by simp [hux, huy]⟩) =
      C0 (some ⟨v.1, by simp [hvx, hvy]⟩)
    simpa only [CommonNeighbor.toDeletedPair] using heq
  let CQ := pairGraphColoringOfEqual hux huy hvx hvy huv c heq'
  obtain ⟨z, hzx, hzy, hzcolor⟩ :=
    everyColorOccursOnIdentifiedCommonNeighbors hxy hux huy huv huvNA hncol CQ (C0 none)
  have hzX : z ≠ x := hzx.ne.symm
  have hzY : z ≠ y := hzy.ne.symm
  have hround := pairGraph_roundTrip hux huy hvx hvy huv huvNA c heq'
    (C0 none) z hzX hzY
  have hzEq : C0 (some (⟨z, by simp [hzX, hzY]⟩ : DeletedPair x y)) = C0 none := by
    change c ⟨z, by simp [hzX, hzY]⟩ = C0 none
    rw [← hround]
    exact hzcolor
  exact apexColor_missing_on_commonNeighbors C0
    (⟨z, by simp [hzX, hzY]⟩ : DeletedPair x y) hzx hzy hzEq

end Apex

section HajnalBridge

open Erdos922

variable {V : Type u} [Fintype V]

omit [Fintype V] in
/-- The finite-set independence number agrees with Mathlib's independence
number on the induced subtype graph. -/
theorem indepNum_induce_finset_eq_alphaOn [Finite V] (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S : Set V)).indepNum = alphaOn G S := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  apply Nat.le_antisymm
  · obtain ⟨J, hJ⟩ := (G.induce (S : Set V)).exists_isNIndepSet_indepNum
    let I : Finset V := J.map ⟨Subtype.val, Subtype.val_injective⟩
    have hIS : I ⊆ S := by
      intro z hz
      simp only [I, Finset.mem_map, Function.Embedding.coeFn_mk] at hz
      obtain ⟨w, -, rfl⟩ := hz
      exact w.2
    have hI : G.IsIndepSet I := by
      rw [show (I : Set V) = Subtype.val '' (J : Set (S : Set V)) by
        simp only [I]
        rw [Finset.coe_map]
        rfl]
      rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩ hab
      exact hJ.isIndepSet ha' hb' (Subtype.coe_ne_coe.mp hab)
    have hcard : I.card = (G.induce (S : Set V)).indepNum := by
      simpa [I] using hJ.card_eq
    rw [← hcard]
    exact card_le_alphaOn hIS hI
  · obtain ⟨I, hIS, hI, hcard⟩ := exists_maximum_independent_subset G S
    let J : Finset (S : Set V) := I.subtype (fun z ↦ z ∈ (S : Set V))
    have hfilter : I.filter (fun z ↦ z ∈ S) = I :=
      Finset.filter_eq_self.mpr hIS
    have hJcard : J.card = alphaOn G S := by
      simpa [J, Finset.card_subtype, hfilter] using hcard
    have hJ : (G.induce (S : Set V)).IsIndepSet J := by
      intro a ha b hb hab
      exact hI (by simpa [J] using ha) (by simpa [J] using hb)
        (Subtype.coe_ne_coe.mpr hab)
    rw [← hJcard]
    exact hJ.card_le_indepNum

omit [Fintype V] in
/-- Finset form of Hajnal's lemma, ready for the `J \ A` set in the diamond
argument. -/
theorem exists_mem_all_maximum_independent_subset [Finite V]
    (G : SimpleGraph V) (U : Finset V)
    (hlarge : U.card < 2 * alphaOn G U) :
    ∃ q ∈ U, ∀ I : Finset V, I ⊆ U → G.IsIndepSet I →
      I.card = alphaOn G U → q ∈ I := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype U := Fintype.ofFinite U
  have hcardU : Fintype.card U = U.card := Fintype.card_coe U
  have hindep : (G.induce (U : Set V)).indepNum = alphaOn G U :=
    indepNum_induce_finset_eq_alphaOn G U
  obtain ⟨q, hq⟩ :=
    (G.induce (U : Set V)).exists_mem_all_maximumIndepSet_of_card_lt_two_mul_indepNum
      (by simpa [hcardU, hindep] using hlarge)
  refine ⟨q.1, q.2, ?_⟩
  intro I hIU hI hIcard
  let Isub : Finset (U : Set V) := I.subtype (fun z ↦ z ∈ (U : Set V))
  have hfilter : I.filter (fun z ↦ z ∈ U) = I :=
    Finset.filter_eq_self.mpr hIU
  have hIsubCard : Isub.card = alphaOn G U := by
    simpa [Isub, Finset.card_subtype, hfilter] using hIcard
  have hIsubIndep : (G.induce (U : Set V)).IsIndepSet Isub := by
    intro a ha b hb hab
    exact hI (by simpa [Isub] using ha) (by simpa [Isub] using hb)
      (Subtype.coe_ne_coe.mpr hab)
  have hmax : (G.induce (U : Set V)).IsMaximumIndepSet Isub := by
    refine ⟨hIsubIndep, ?_⟩
    intro T hT
    rw [hIsubCard, ← hindep]
    exact hT.card_le_indepNum
  have hqI : q ∈ Isub := hq Isub hmax
  simpa [Isub] using hqI

/-- Finset of common neighbors of an edge. -/
def commonNeighborFinset (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) : Finset V :=
  Finset.univ.filter fun z ↦ G.Adj x z ∧ G.Adj y z

@[simp] theorem mem_commonNeighborFinset {G : SimpleGraph V}
    [DecidableRel G.Adj] {x y z : V} :
    z ∈ commonNeighborFinset G x y ↔ G.Adj x z ∧ G.Adj y z := by
  simp [commonNeighborFinset]

/-- The final Hajnal contradiction in the no-diamond argument.  The inputs
are exactly the properties established for the old-vertex witness `J` of the
apex graph: it attains `f(G)`, deleting common neighbors does not lower its
independence number, and the remaining set has size less than twice that
number. -/
theorem hajnal_apexWitness_contradiction
    (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]
    (x y : V) (J : Finset V)
    (hxy : G.Adj x y) (hxJ : x ∉ J) (hyJ : y ∉ J)
    (halpha : alphaOn G (J \ commonNeighborFinset G x y) = alphaOn G J)
    (hlarge : (J \ commonNeighborFinset G x y).card <
      2 * alphaOn G (J \ commonNeighborFinset G x y))
    (hmax : potential G J = f G) : False := by
  classical
  let A := commonNeighborFinset G x y
  let U := J \ A
  let a := alphaOn G J
  obtain ⟨q, hqU, hqall⟩ :=
    exists_mem_all_maximum_independent_subset G U (by simpa [U, A] using hlarge)
  have hqJ : q ∈ J := (Finset.mem_sdiff.mp hqU).1
  have hqx : q ≠ x := fun h ↦ hxJ (h ▸ hqJ)
  have hqy : q ≠ y := fun h ↦ hyJ (h ▸ hqJ)
  let H : Finset V := insert x (insert y (J.erase q))
  have hHcard : H.card = J.card + 1 := by
    have herase := Finset.card_erase_add_one hqJ
    simp [H, hxJ, hyJ, hqJ, hxy.ne]
    omega
  have hpH := potential_le_f G H
  rw [← hmax] at hpH
  have halphaH : a + 1 ≤ alphaOn G H := by
    rw [potential, potential, hHcard] at hpH
    simp only [a]
    omega
  obtain ⟨I, hIH, hI, hIcard⟩ := exists_maximum_independent_subset G H
  have hIlarge : a + 1 ≤ I.card := by omega
  let P : Finset V := {x, y}
  let Iold : Finset V := I \ P
  have hIold_sub_erase : Iold ⊆ J.erase q := by
    intro z hz
    have hzI : z ∈ I := (Finset.mem_sdiff.mp hz).1
    have hzP : z ∉ P := (Finset.mem_sdiff.mp hz).2
    have hzH : z ∈ H := hIH hzI
    simp only [H, Finset.mem_insert] at hzH
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hzP
    have hzX : z ≠ x := fun h ↦ hzP (Or.inl h)
    have hzY : z ≠ y := fun h ↦ hzP (Or.inr h)
    have hzErase : z ∈ J.erase q := by
      rcases hzH with h | h | h
      · exact (hzX h).elim
      · exact (hzY h).elim
      · exact h
    exact hzErase
  have hIold_indep : G.IsIndepSet Iold := hI.mono (by intro z hz; exact (Finset.mem_sdiff.mp hz).1)
  have hIold_le : Iold.card ≤ a := by
    exact card_le_alphaOn (hIold_sub_erase.trans (Finset.erase_subset q J)) hIold_indep
  have hIP_le : (I ∩ P).card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro r s hr hs
    have hrI : r ∈ I := (Finset.mem_inter.mp hr).1
    have hsI : s ∈ I := (Finset.mem_inter.mp hs).1
    have hrP := (Finset.mem_inter.mp hr).2
    have hsP := (Finset.mem_inter.mp hs).2
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hrP hsP
    rcases hrP with rfl | rfl <;> rcases hsP with rfl | rfl
    · rfl
    · exact (hI hrI hsI hxy.ne hxy).elim
    · exact (hI hrI hsI hxy.ne.symm hxy.symm).elim
    · rfl
  have hsplit := Finset.card_sdiff_add_card_inter I P
  have hsplit' : Iold.card + (I ∩ P).card = I.card := by
    exact hsplit
  have hIold_eq : Iold.card = a := by
    omega
  have hIP_nonempty : (I ∩ P).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [he] at hsplit'
    simp only [Finset.card_empty, add_zero] at hsplit'
    omega
  obtain ⟨t, ht⟩ := hIP_nonempty
  obtain ⟨htI, htP⟩ := Finset.mem_inter.mp ht
  have ht : t = x ∨ t = y := by simpa [P] using htP
  have hIold_sub_U : Iold ⊆ U := by
    intro z hz
    have hzErase := hIold_sub_erase hz
    rw [Finset.mem_sdiff]
    refine ⟨(Finset.mem_erase.mp hzErase).2, ?_⟩
    intro hzA
    have hzCommon := mem_commonNeighborFinset.mp hzA
    have hzI : z ∈ I := (Finset.mem_sdiff.mp hz).1
    have htz : t ≠ z := by
      rintro rfl
      exact (Finset.mem_sdiff.mp hz).2 htP
    rcases ht with rfl | rfl
    · exact hI htI hzI htz hzCommon.1
    · exact hI htI hzI htz hzCommon.2
  have hIoldAlpha : Iold.card = alphaOn G U := by
    rw [hIold_eq]
    simpa [U, A, a] using halpha.symm
  have hqIold := hqall Iold hIold_sub_U hIold_indep hIoldAlpha
  exact (Finset.mem_erase.mp (hIold_sub_erase hqIold)).1 rfl

end HajnalBridge

end Erdos922Diamond
