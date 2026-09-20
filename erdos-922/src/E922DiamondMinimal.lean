/-
Inherited Folkman/Erdos922 proof, original lines 2535--3768.
plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos922.lean, SHA256
0bc22004ecbe76ab3cc3f263c29c76994b39017828ea835d987139fa324b9971.
Original informal author: Jon Folkman. Formal authors: Codex; GPT-5.6 Sol.
Local Lean4.19 port under Gott-L's direction, with Codex/B implementation.
Private experiment; upstream license not verified. No mathematical novelty claim.
-/
import E922DiamondCore

open SimpleGraph
open scoped ENat


namespace Erdos922Diamond

section MinimalCounterexampleDiamond

open Erdos922

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y u v : V}

/-- The retained quotient vertices, embedded back into the original vertex type. -/
def identifiedPairEmbedding (x y v : V) : IdentifiedPair x y v ↪ V where
  toFun z := z.1.1
  inj' := fun _ _ h => Subtype.ext (Subtype.ext h)

/-- The old vertices represented by a quotient finset. -/
def pairLiftBase (x y v : V) (S : Finset (IdentifiedPair x y v)) : Finset V :=
  S.map (identifiedPairEmbedding x y v)

omit [DecidableEq V] [Fintype V] in
@[simp] theorem mem_pairLiftBase [Finite V] {S : Finset (IdentifiedPair x y v)} {z : V} :
    z ∈ pairLiftBase x y v S ↔
      ∃ q ∈ S, q.1.1 = z := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rw [pairLiftBase, Finset.mem_map]
  constructor
  · rintro ⟨q, hq, hqz⟩
    exact ⟨q, hq, hqz⟩
  · rintro ⟨q, hq, hqz⟩
    exact ⟨q, hq, hqz⟩

omit [DecidableEq V] [Fintype V] in
@[simp] theorem pairLiftBase_card [Finite V] (S : Finset (IdentifiedPair x y v)) :
    (pairLiftBase x y v S).card = S.card := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  simp [pairLiftBase]

/-- The quotient representative corresponding to `u`. -/
def pairRepresentative (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v) :
    IdentifiedPair x y v :=
  ⟨⟨u, by simp [hux, huy]⟩, huv⟩

omit [DecidableEq V] [Fintype V] in
@[simp] theorem pairRepresentative_val [Finite V]
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v) :
    (pairRepresentative hux huy huv).1.1 = u := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  exact rfl

omit [DecidableEq V] [Fintype V] in
theorem pairRepresentative_mem_iff [Finite V]
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) :
    pairRepresentative hux huy huv ∈ S ↔ u ∈ pairLiftBase x y v S := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  constructor
  · intro h
    exact mem_pairLiftBase.mpr ⟨_, h, rfl⟩
  · intro h
    obtain ⟨q, hq, hqv⟩ := mem_pairLiftBase.mp h
    have : q = pairRepresentative hux huy huv := by
      exact Subtype.ext (Subtype.ext hqv)
    simpa [this] using hq

/-- The witness lift for a quotient finset.  The quotient representative is
expanded to `u,v`; when absent, `u` is used as the third vertex of the added
triangle. -/
def pairWitnessLift
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) : Finset V :=
  if pairRepresentative hux huy huv ∈ S then
    insert x (insert y (insert v (pairLiftBase x y v S)))
  else
    insert x (insert y (insert u (pairLiftBase x y v S)))

omit [DecidableRel G.Adj] [Fintype V] in
theorem pairWitnessLift_card [Finite V]
    (hxy : G.Adj x y)
    (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v)
    (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) :
    (pairWitnessLift hxu.ne.symm hyu.ne.symm huv S).card = S.card + 3 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hux : u ≠ x := hxu.ne.symm
  have huy : u ≠ y := hyu.ne.symm
  have hvx : v ≠ x := hxv.ne.symm
  have hvy : v ≠ y := hyv.ne.symm
  have hxB : x ∉ pairLiftBase x y v S := by
    rintro hx
    obtain ⟨q, -, hq⟩ := mem_pairLiftBase.mp hx
    exact q.1.2 (by simp [hq])
  have hyB : y ∉ pairLiftBase x y v S := by
    rintro hy
    obtain ⟨q, -, hq⟩ := mem_pairLiftBase.mp hy
    exact q.1.2 (by simp [hq])
  have hvB : v ∉ pairLiftBase x y v S := by
    rintro hv
    obtain ⟨q, -, hq⟩ := mem_pairLiftBase.mp hv
    exact q.2 hq
  by_cases hw : pairRepresentative hux huy huv ∈ S
  · have hw' : pairRepresentative hxu.ne.symm hyu.ne.symm huv ∈ S := by
      simpa [pairRepresentative] using hw
    rw [pairWitnessLift, if_pos hw']
    have hvcard : (insert v (pairLiftBase x y v S)).card =
        (pairLiftBase x y v S).card + 1 := Finset.card_insert_of_not_mem hvB
    have hycard : (insert y (insert v (pairLiftBase x y v S))).card =
        (insert v (pairLiftBase x y v S)).card + 1 := by
      apply Finset.card_insert_of_not_mem
      simp [hyv.ne, hyB]
    have hxcard : (insert x (insert y (insert v (pairLiftBase x y v S)))).card =
        (insert y (insert v (pairLiftBase x y v S))).card + 1 := by
      apply Finset.card_insert_of_not_mem
      simp [hxy.ne, hxv.ne, hxB]
    rw [hxcard, hycard, hvcard, pairLiftBase_card]
  · have huB : u ∉ pairLiftBase x y v S := by
      simpa [pairRepresentative_mem_iff hux huy huv S] using hw
    have hw' : pairRepresentative hxu.ne.symm hyu.ne.symm huv ∉ S := by
      simpa [pairRepresentative] using hw
    rw [pairWitnessLift, if_neg hw']
    have hucard : (insert u (pairLiftBase x y v S)).card =
        (pairLiftBase x y v S).card + 1 := Finset.card_insert_of_not_mem huB
    have hycard : (insert y (insert u (pairLiftBase x y v S))).card =
        (insert u (pairLiftBase x y v S)).card + 1 := by
      apply Finset.card_insert_of_not_mem
      simp [hyu.ne, hyB]
    have hxcard : (insert x (insert y (insert u (pairLiftBase x y v S)))).card =
        (insert y (insert u (pairLiftBase x y v S))).card + 1 := by
      apply Finset.card_insert_of_not_mem
      simp [hxy.ne, hxu.ne, hxB]
    rw [hxcard, hycard, hucard, pairLiftBase_card]

/-- Vertices outside the four distinguished vertices of a diamond. -/
abbrev OutsideFour (x y u v : V) :=
  {z : V // z ≠ x ∧ z ≠ y ∧ z ≠ u ∧ z ≠ v}

/-- An outside vertex is unchanged by pair identification. -/
def outsideFourToIdentified
    (x y u v : V) : OutsideFour x y u v ↪ IdentifiedPair x y v where
  toFun z := ⟨⟨z.1, by simp [z.2.1, z.2.2.1]⟩, z.2.2.2.2⟩
  inj' := fun _ _ h => Subtype.ext (congrArg (fun q => q.1.1) h)

/-- Outside members of a finset, bundled with their non-membership proofs. -/
def outsideFourFinset (x y u v : V) (I : Finset V) :
    Finset (OutsideFour x y u v) :=
  I.subtype (fun z => z ≠ x ∧ z ≠ y ∧ z ≠ u ∧ z ≠ v)

/-- The quotient independent-set candidate used in the witness lift. -/
def pairCompressedSet
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (I : Finset V) : Finset (IdentifiedPair x y v) :=
  let O := (outsideFourFinset x y u v I).map
    (outsideFourToIdentified x y u v)
  if u ∈ I ∧ v ∈ I then insert (pairRepresentative hux huy huv) O else O

omit [Fintype V] in
@[simp] theorem mem_outsideFourFinset [Finite V] {I : Finset V} {z : OutsideFour x y u v} :
    z ∈ outsideFourFinset x y u v I ↔ z.1 ∈ I := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  simp [outsideFourFinset]

omit [Fintype V] in
@[simp] theorem outsideFourFinset_card [Finite V] (I : Finset V) :
    (outsideFourFinset x y u v I).card =
      (I \ {x, y, u, v}).card := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  simp only [outsideFourFinset, Finset.card_subtype]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_insert,
    Finset.mem_singleton]
  tauto

omit [DecidableEq V] [Fintype V] in
theorem pairIdentify_eq_representative_iff [Finite V]
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (z : DeletedPair x y) :
    pairIdentify x y u v hux huy huv z = pairRepresentative hux huy huv ↔
      z.1 = u ∨ z.1 = v := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  by_cases hzv : z.1 = v
  · simp [pairIdentify, pairRepresentative, hzv]
  · simp only [pairIdentify, dif_neg hzv, pairRepresentative]
    constructor
    · intro h
      left
      exact congrArg (fun q : IdentifiedPair x y v => q.1.1) h
    · rintro (hzu | hzu)
      · exact Subtype.ext (Subtype.ext hzu)
      · exact (hzv hzu).elim

omit [DecidableEq V] [Fintype V] in
theorem pairIdentify_eq_outside [Finite V]
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (z : DeletedPair x y) (a : OutsideFour x y u v)
    (h : pairIdentify x y u v hux huy huv z = outsideFourToIdentified x y u v a) :
    z.1 = a.1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  by_cases hzv : z.1 = v
  · have hvu := congrArg (fun q : IdentifiedPair x y v => q.1.1) h
    simp [pairIdentify, hzv, outsideFourToIdentified] at hvu
    exact (a.2.2.2.1 hvu.symm).elim
  · have hza := congrArg (fun q : IdentifiedPair x y v => q.1.1) h
    rw [pairIdentify, dif_neg hzv] at hza
    change z.1 = a.1 at hza
    exact hza

omit [Fintype V] in
theorem outside_mem_S_of_mem_pairWitnessLift [Finite V]
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) (a : OutsideFour x y u v)
    (ha : a.1 ∈ pairWitnessLift hux huy huv S) :
    outsideFourToIdentified x y u v a ∈ S := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  by_cases hw : pairRepresentative hux huy huv ∈ S
  · simp only [pairWitnessLift, hw, if_pos] at ha
    have haB : a.1 ∈ pairLiftBase x y v S := by
      simpa [a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2] using ha
    obtain ⟨q, hqS, hq⟩ := mem_pairLiftBase.mp haB
    have hqa : q = outsideFourToIdentified x y u v a := by
      exact Subtype.ext (Subtype.ext hq)
    simpa [hqa] using hqS
  · simp only [pairWitnessLift, hw] at ha
    have haB : a.1 ∈ pairLiftBase x y v S := by
      simpa [a.2.1, a.2.2.1, a.2.2.2.1] using ha
    obtain ⟨q, hqS, hq⟩ := mem_pairLiftBase.mp haB
    have hqa : q = outsideFourToIdentified x y u v a := by
      exact Subtype.ext (Subtype.ext hq)
    simpa [hqa] using hqS

omit [DecidableRel G.Adj] [Fintype V] in
theorem pairRepresentative_mem_of_both_mem_pairWitnessLift [Finite V]
    (_hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v))
    (_huI : u ∈ pairWitnessLift hxu.ne.symm hyu.ne.symm huv S)
    (hvI : v ∈ pairWitnessLift hxu.ne.symm hyu.ne.symm huv S) :
    pairRepresentative hxu.ne.symm hyu.ne.symm huv ∈ S := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  by_contra hw
  have hvB : v ∉ pairLiftBase x y v S := by
    rintro hv
    obtain ⟨q, -, hq⟩ := mem_pairLiftBase.mp hv
    exact q.2 hq
  simp only [pairWitnessLift, hw] at hvI
  simp [hxv.ne.symm, hyv.ne.symm, huv.symm, hvB] at hvI

omit [DecidableRel G.Adj] [Fintype V] in
theorem pairCompressedSet_subset [Finite V]
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) (I : Finset V)
    (hIH : I ⊆ pairWitnessLift hxu.ne.symm hyu.ne.symm huv S) :
    pairCompressedSet hxu.ne.symm hyu.ne.symm huv I ⊆ S := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  intro q hq
  by_cases hboth : u ∈ I ∧ v ∈ I
  · rw [pairCompressedSet, if_pos hboth] at hq
    simp only [Finset.mem_insert] at hq
    rcases hq with hqrep | hqout
    · subst q
      exact pairRepresentative_mem_of_both_mem_pairWitnessLift hxy hxu hyu hxv hyv huv S
        (hIH hboth.1) (hIH hboth.2)
    · rw [Finset.mem_map] at hqout
      obtain ⟨a, haI, rfl⟩ := hqout
      exact outside_mem_S_of_mem_pairWitnessLift hxu.ne.symm hyu.ne.symm huv S a
        (hIH (mem_outsideFourFinset.mp haI))
  · rw [pairCompressedSet, if_neg hboth] at hq
    rw [Finset.mem_map] at hq
    obtain ⟨a, haI, rfl⟩ := hq
    exact outside_mem_S_of_mem_pairWitnessLift hxu.ne.symm hyu.ne.symm huv S a
      (hIH (mem_outsideFourFinset.mp haI))

omit [Fintype V] in
theorem source_mem_of_pairIdentify_mem_pairCompressedSet [Finite V]
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (I : Finset V) (z : DeletedPair x y)
    (hz : pairIdentify x y u v hux huy huv z ∈
      pairCompressedSet hux huy huv I) : z.1 ∈ I := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  by_cases hboth : u ∈ I ∧ v ∈ I
  · rw [pairCompressedSet, if_pos hboth] at hz
    simp only [Finset.mem_insert] at hz
    rcases hz with hzrep | hzout
    · rcases (pairIdentify_eq_representative_iff hux huy huv z).mp hzrep with hzu | hzv
      · simpa [hzu] using hboth.1
      · simpa [hzv] using hboth.2
    · rw [Finset.mem_map] at hzout
      obtain ⟨a, haI, hza⟩ := hzout
      have hzval := pairIdentify_eq_outside hux huy huv z a hza.symm
      simpa [hzval] using (mem_outsideFourFinset.mp haI)
  · rw [pairCompressedSet, if_neg hboth] at hz
    rw [Finset.mem_map] at hz
    obtain ⟨a, haI, hza⟩ := hz
    have hzval := pairIdentify_eq_outside hux huy huv z a hza.symm
    simpa [hzval] using (mem_outsideFourFinset.mp haI)

omit [DecidableRel G.Adj] [Fintype V] in
theorem pairCompressedSet_indep [Finite V]
    (hux : u ≠ x) (huy : u ≠ y) (huv : u ≠ v)
    (I : Finset V) (hI : G.IsIndepSet I) :
    (pairGraph (G := G) hux huy huv).IsIndepSet
      (pairCompressedSet hux huy huv I) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  intro a ha b hb hab hAdj
  rcases hAdj with
    ⟨-, a', b', hab', ha', hb'⟩
  have haI : a'.1 ∈ I := source_mem_of_pairIdentify_mem_pairCompressedSet
    hux huy huv I a' (ha' ▸ ha)
  have hbI : b'.1 ∈ I := source_mem_of_pairIdentify_mem_pairCompressedSet
    hux huy huv I b' (hb' ▸ hb)
  exact hI haI hbI (Subtype.coe_ne_coe.mpr hab'.ne) hab'

omit [DecidableRel G.Adj] [Fintype V] in
theorem pairCompressedSet_card_bound [Finite V]
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (I : Finset V) (hI : G.IsIndepSet I) :
    I.card ≤ (pairCompressedSet hxu.ne.symm hyu.ne.symm huv I).card + 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let P : Finset V := {x, y, u, v}
  have hsplit := Finset.card_sdiff_add_card_inter I P
  have hsplit' : (I \ P).card + (I ∩ P).card = I.card := by
    exact hsplit
  by_cases hboth : u ∈ I ∧ v ∈ I
  · have hxI : x ∉ I := by
      intro hxI
      exact hI hxI hboth.1 hxu.ne hxu
    have hyI : y ∉ I := by
      intro hyI
      exact hI hyI hboth.1 hyu.ne hyu
    have hinter : I ∩ P = {u, v} := by
      ext z
      simp only [P, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hzI, hz⟩
        rcases hz with rfl | rfl | rfl | rfl
        · exact (hxI hzI).elim
        · exact (hyI hzI).elim
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨hboth.1, Or.inr (Or.inr (Or.inl rfl))⟩
        · exact ⟨hboth.2, Or.inr (Or.inr (Or.inr rfl))⟩
    have hrep_not : pairRepresentative hxu.ne.symm hyu.ne.symm huv ∉
        (outsideFourFinset x y u v I).map (outsideFourToIdentified x y u v) := by
      intro h
      rw [Finset.mem_map] at h
      obtain ⟨a, -, ha⟩ := h
      have hau := congrArg (fun q : IdentifiedPair x y v => q.1.1) ha
      have haVal : (outsideFourToIdentified x y u v a).1.1 = a.1 := rfl
      have hrVal : (pairRepresentative hxu.ne.symm hyu.ne.symm huv).1.1 = u := rfl
      have hau' : a.1 = u := by
        change a.1 = u at hau
        exact hau
      exact a.2.2.2.1 hau'
    have hcardC : (pairCompressedSet hxu.ne.symm hyu.ne.symm huv I).card =
        (I \ P).card + 1 := by
      rw [pairCompressedSet, if_pos hboth]
      rw [Finset.card_insert_of_not_mem hrep_not, Finset.card_map, outsideFourFinset_card]
    rw [hinter] at hsplit'
    have hPcard : ({u, v} : Finset V).card = 2 := by simp [huv]
    rw [hPcard] at hsplit'
    rw [hcardC]
    omega
  · have hinter_le : (I ∩ P).card ≤ 1 := by
      rw [Finset.card_le_one_iff]
      intro r s hr hs
      obtain ⟨hrI, hrP⟩ := Finset.mem_inter.mp hr
      obtain ⟨hsI, hsP⟩ := Finset.mem_inter.mp hs
      simp only [P, Finset.mem_insert, Finset.mem_singleton] at hrP hsP
      rcases hrP with rfl | rfl | rfl | rfl <;>
        rcases hsP with rfl | rfl | rfl | rfl
      all_goals try rfl
      all_goals first
        | exact (hI hrI hsI hxy.ne hxy).elim
        | exact (hI hrI hsI hxy.ne.symm hxy.symm).elim
        | exact (hI hrI hsI hxu.ne hxu).elim
        | exact (hI hrI hsI hxu.ne.symm hxu.symm).elim
        | exact (hI hrI hsI hyu.ne hyu).elim
        | exact (hI hrI hsI hyu.ne.symm hyu.symm).elim
        | exact (hI hrI hsI hxv.ne hxv).elim
        | exact (hI hrI hsI hxv.ne.symm hxv.symm).elim
        | exact (hI hrI hsI hyv.ne hyv).elim
        | exact (hI hrI hsI hyv.ne.symm hyv.symm).elim
        | exact (hboth ⟨hrI, hsI⟩).elim
        | exact (hboth ⟨hsI, hrI⟩).elim
    have hcardC : (pairCompressedSet hxu.ne.symm hyu.ne.symm huv I).card =
        (I \ P).card := by
      rw [pairCompressedSet, if_neg hboth, Finset.card_map, outsideFourFinset_card]
    rw [hcardC]
    omega

omit [DecidableRel G.Adj] [Fintype V] in
/-- Every independent set in the lifted witness compresses to an independent
set of the quotient while losing at most one vertex. -/
theorem alphaOn_pairWitnessLift_le [Finite V]
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) :
    alphaOn G (pairWitnessLift hxu.ne.symm hyu.ne.symm huv S) ≤
      alphaOn (pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv) S + 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨I, hIH, hI, hIcard⟩ :=
    exists_maximum_independent_subset G
      (pairWitnessLift hxu.ne.symm hyu.ne.symm huv S)
  let J := pairCompressedSet hxu.ne.symm hyu.ne.symm huv I
  have hJS : J ⊆ S := pairCompressedSet_subset hxy hxu hyu hxv hyv huv S I hIH
  have hJind : (pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv).IsIndepSet J :=
    pairCompressedSet_indep hxu.ne.symm hyu.ne.symm huv I hI
  have hJalpha : J.card ≤
      alphaOn (pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv) S :=
    card_le_alphaOn hJS hJind
  have hcard := pairCompressedSet_card_bound hxy hxu hyu hxv hyv huv I hI
  rw [← hIcard]
  exact hcard.trans (Nat.add_le_add_right hJalpha 1)

omit [DecidableRel G.Adj] [Fintype V] in
/-- Each quotient witness gains at least one unit of signed potential when
lifted back to the four diamond vertices. -/
theorem pairGraph_potential_add_one_le [Finite V]
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (S : Finset (IdentifiedPair x y v)) :
    potential (pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv) S + 1 ≤
      potential G (pairWitnessLift hxu.ne.symm hyu.ne.symm huv S) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hcard := pairWitnessLift_card hxy hxu hyu hxv hyv huv S
  have halpha := alphaOn_pairWitnessLift_le hxy hxu hyu hxv hyv huv S
  rw [potential, potential, hcard]
  omega

omit [DecidableRel G.Adj] in
/-- C1.1's potential estimate: identifying the two nonadjacent common
neighbors after deleting the edge endpoints lowers `f` by at least one. -/
theorem pairGraph_f_le_sub_one
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v) :
    f (pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv) ≤ f G - 1 := by
  classical
  rw [f_le_iff_forall_potential_le]
  intro S
  have hlift := pairGraph_potential_add_one_le hxy hxu hyu hxv hyv huv S
  have hmax := potential_le_f G (pairWitnessLift hxu.ne.symm hyu.ne.symm huv S)
  omega

/-- The pair quotient is strictly smaller than the original graph. -/
theorem pairGraph_card_lt
    (_hux : u ≠ x) (_huy : u ≠ y) (_huv : u ≠ v) :
    Fintype.card (IdentifiedPair x y v) < Fintype.card V := by
  apply Fintype.card_lt_of_injective_not_surjective
    (identifiedPairEmbedding x y v) (identifiedPairEmbedding x y v).injective
  intro hsurj
  obtain ⟨q, hq⟩ := hsurj x
  have hval : identifiedPairEmbedding x y v q = q.1.1 := rfl
  rw [hval] at hq
  exact q.1.2 (Or.inl hq)

/-- Embed the apex construction into `V`, sending the apex to `x`. -/
def apexIntoOriginal (x y : V) : Option (DeletedPair x y) ↪ V where
  toFun z := match z with
    | none => x
    | some w => w.1
  inj' := by
    intro a b h
    cases a with
    | none =>
        cases b with
        | none => rfl
        | some b => exact (b.2 (Or.inl (by simpa using h.symm))).elim
    | some a =>
        cases b with
        | none => exact (a.2 (Or.inl (by simpa using h))).elim
        | some b => exact congrArg some (Subtype.ext h)

omit [DecidableRel G.Adj] in
/-- The apex construction is strictly smaller, since `y` is not in the
image of `apexIntoOriginal`. -/
theorem commonNeighborApexGraph_card_lt (hxy : G.Adj x y) :
    Fintype.card (Option (DeletedPair x y)) < Fintype.card V := by
  classical
  apply Fintype.card_lt_of_injective_not_surjective
    (apexIntoOriginal x y) (apexIntoOriginal x y).injective
  intro hsurj
  obtain ⟨z, hz⟩ := hsurj y
  cases z with
  | none => exact hxy.ne hz
  | some z =>
      have hval : apexIntoOriginal x y (some z) = z.1 := rfl
      rw [hval] at hz
      exact z.2 (Or.inr hz)

/-- A coloring by an arbitrary finite type is equivalent to colorability by
the cardinality of that type. -/
theorem nonempty_coloring_iff_colorable_card {W : Type u} (H : SimpleGraph W)
    {α : Type v} [Fintype α] :
    Nonempty (H.Coloring α) ↔ H.Colorable (Fintype.card α) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨SimpleGraph.recolorOfEquiv H (Fintype.equivFin α) C⟩
  · rintro ⟨C⟩
    exact ⟨SimpleGraph.recolorOfEquiv H (Fintype.equivFin α).symm C⟩

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- C1.1 in the form used by C1.2: the pair quotient has an
`(chiNat G - 2)`-coloring. -/
theorem pairGraph_colorable_chi_sub_two
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v) :
    (pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv).Colorable
      (Erdos922FullB.chiNat G - 2) := by
  classical
  let Q := pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv
  have hsmall := hmin.smaller Q
    (pairGraph_card_lt hxu.ne.symm hyu.ne.symm huv)
  change Q.Colorable (Int.toNat (f Q) + 2) at hsmall
  have hfQ := pairGraph_f_le_sub_one hxy hxu hyu hxv hyv huv
  have hgap := Erdos922FullB.counterexample_gap_int G hmin.counterexample
  change f G + 2 < (Erdos922FullB.chiNat G : ℤ) at hgap
  have hfQ0 := f_nonneg Q
  have hfG0 := f_nonneg G
  change f Q ≤ f G - 1 at hfQ
  change 0 ≤ f Q at hfQ0
  have hfQcast : (Int.toNat (f Q) : ℤ) = f Q := Int.toNat_of_nonneg hfQ0
  have hchi := Erdos922FullB.three_le_chiNat_of_not_folkmanBound G hmin.counterexample
  apply hsmall.mono
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A minimal counterexample has no coloring using one fewer color than its
chromatic number, with `Option` supplying the fresh color. -/
theorem not_coloring_option_chi_sub_two
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G) :
    ¬ Nonempty (G.Coloring (Option (Fin (Erdos922FullB.chiNat G - 2)))) := by
  classical
  intro hC
  have hc := (nonempty_coloring_iff_colorable_card G).mp hC
  have hchi := Erdos922FullB.three_le_chiNat_of_not_folkmanBound G hmin.counterexample
  have hcard : Fintype.card (Option (Fin (Erdos922FullB.chiNat G - 2))) =
      Erdos922FullB.chiNat G - 1 := by
    simp
    omega
  rw [hcard] at hc
  have hle := (Erdos922FullB.colorable_iff_chiNat_le G _).mp hc
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- C1.2 plus the identified pair show that an edge has strictly more common
neighbors than the quotient palette. -/
theorem chi_sub_two_lt_commonNeighbors
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v) :
    Erdos922FullB.chiNat G - 2 < Nat.card (CommonNeighbor G x y) := by
  classical
  let α := Fin (Erdos922FullB.chiNat G - 2)
  let Q := pairGraph (G := G) hxu.ne.symm hyu.ne.symm huv
  let C : Q.Coloring α := Classical.choice
    (pairGraph_colorable_chi_sub_two hmin hxy hxu hyu hxv hyv huv)
  let color : CommonNeighbor G x y → α := fun z =>
    C (pairIdentify x y u v hxu.ne.symm hyu.ne.symm huv z.toDeletedPair)
  have hchi := Erdos922FullB.three_le_chiNat_of_not_folkmanBound G hmin.counterexample
  have hsurj : Function.Surjective color := by
    intro i
    obtain ⟨z, hzx, hzy, hzi⟩ := everyColorOccursOnIdentifiedCommonNeighbors
      hxy hxu.ne.symm hyu.ne.symm huv huvNA
      (not_coloring_option_chi_sub_two hmin) C i
    refine ⟨⟨z, hzx, hzy⟩, ?_⟩
    have hzx' : z ≠ x := hzx.ne.symm
    have hzy' : z ≠ y := hzy.ne.symm
    have hzOld : z ∈ ({x, y}ᶜ : Set V) := by simp [hzx', hzy']
    simp only [pairGraphPullFunction, hzOld, dif_pos] at hzi
    change C (pairIdentify x y u v hxu.ne.symm hyu.ne.symm huv
      ⟨z, hzOld⟩) = i at hzi
    simpa [color, CommonNeighbor.toDeletedPair, hzx', hzy'] using hzi
  let cu : CommonNeighbor G x y := ⟨u, hxu, hyu⟩
  let cv : CommonNeighbor G x y := ⟨v, hxv, hyv⟩
  have hcucv : color cu = color cv := by
    dsimp only [color, cu, cv, CommonNeighbor.toDeletedPair]
    simp [pairIdentify, huv]
  have hnotinj : ¬ Function.Injective color := by
    intro hinj
    have := hinj hcucv
    exact huv (congrArg Subtype.val this)
  letI : Fintype (CommonNeighbor G x y) := Fintype.ofFinite _
  have hlt := Fintype.card_lt_of_surjective_not_injective color hsurj hnotinj
  simpa [α, Nat.card_eq_fintype_card] using hlt

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The common-neighbor apex graph cannot use `chiNat G - 2` colors. -/
theorem apex_not_colorable_chi_sub_two
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v) :
    ¬ (commonNeighborApexGraph (G := G) (x := x) (y := y)).Colorable
      (Erdos922FullB.chiNat G - 2) := by
  classical
  intro hc
  apply commonNeighborApexGraph_not_colorable hxy
    (not_coloring_option_chi_sub_two hmin)
    (by simpa using
      chi_sub_two_lt_commonNeighbors hmin hxy hxu hyu hxv hyv huv huvNA)
  apply (nonempty_coloring_iff_colorable_card _).mpr
  simpa using hc

omit [DecidableRel G.Adj] in
/-- Minimality and apex noncolorability force the apex graph's potential
maximum to be at least that of `G`. -/
theorem f_le_f_apex
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (hxy : G.Adj x y) (hxu : G.Adj x u) (hyu : G.Adj y u)
    (hxv : G.Adj x v) (hyv : G.Adj y v) (huv : u ≠ v)
    (huvNA : ¬ G.Adj u v) :
    f G ≤ f (commonNeighborApexGraph (G := G) (x := x) (y := y)) := by
  classical
  let G0 := commonNeighborApexGraph (G := G) (x := x) (y := y)
  have hsmall := hmin.smaller G0 (commonNeighborApexGraph_card_lt hxy)
  change G0.Colorable (Int.toNat (f G0) + 2) at hsmall
  have hncol := apex_not_colorable_chi_sub_two hmin hxy hxu hyu hxv hyv huv huvNA
  have hpalette : Erdos922FullB.chiNat G - 2 < Int.toNat (f G0) + 2 := by
    by_contra h
    exact hncol (hsmall.mono (by omega))
  have hgap := Erdos922FullB.counterexample_gap_int G hmin.counterexample
  change f G + 2 < (Erdos922FullB.chiNat G : ℤ) at hgap
  have hf0 := f_nonneg G0
  have hfG := f_nonneg G
  have hf0cast : (Int.toNat (f G0) : ℤ) = f G0 := Int.toNat_of_nonneg hf0
  have hfGcast : (Int.toNat (f G) : ℤ) = f G := Int.toNat_of_nonneg hfG
  have hchi := Erdos922FullB.three_le_chiNat_of_not_folkmanBound G hmin.counterexample
  have hfGle : f G ≤ (Erdos922FullB.chiNat G : ℤ) - 3 := by omega
  have hf0ge : (Erdos922FullB.chiNat G : ℤ) - 3 ≤ f G0 := by omega
  exact hfGle.trans hf0ge

/-- Non-apex vertices, carrying the proof needed to eliminate the `none`
case. -/
abbrev NonApex (x y : V) := {z : Option (DeletedPair x y) // z ≠ none}

/-- Forget `some` and embed a non-apex vertex into `V`. -/
def nonApexIntoOriginal (x y : V) : NonApex x y ↪ V where
  toFun z := match h : z.1 with
    | none => (z.2 h).elim
    | some w => w.1
  inj' := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
    cases a with
    | none => exact (ha rfl).elim
    | some a' =>
        cases b with
        | none => exact (hb rfl).elim
        | some b' =>
            apply Subtype.ext
            apply congrArg some
            apply Subtype.ext
            exact hab

omit [DecidableEq V] in
/-- Old vertices represented by a finset of the apex graph. -/
noncomputable def apexOldPart (x y : V) (S : Finset (Option (DeletedPair x y))) : Finset V := by
  classical
  letI : DecidableEq V := Classical.decEq V
  exact (S.subtype (fun z => z ≠ none)).map (nonApexIntoOriginal x y)

omit [DecidableEq V] [Fintype V] in
@[simp] theorem mem_apexOldPart [Finite V] {S : Finset (Option (DeletedPair x y))} {z : V} :
    z ∈ apexOldPart x y S ↔
      ∃ d : DeletedPair x y, some d ∈ S ∧ d.1 = z := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  constructor
  · intro hz
    rw [apexOldPart, Finset.mem_map] at hz
    obtain ⟨q, hq, hqz⟩ := hz
    have hqS : q.1 ∈ S := by simpa using hq
    cases heq : q.1 with
    | none => exact (q.2 heq).elim
    | some d =>
        have qeq : q = (⟨some d, by simp⟩ : NonApex x y) := Subtype.ext heq
        subst q
        have hd : d.1 = z := by
          change d.1 = z at hqz
          exact hqz
        exact ⟨d, by simpa [heq] using hqS, hd⟩
  · rintro ⟨d, hdS, rfl⟩
    rw [apexOldPart, Finset.mem_map]
    let q : NonApex x y := ⟨some d, by simp⟩
    refine ⟨q, ?_, ?_⟩
    · simpa [q] using hdS
    · rfl

omit [DecidableEq V] [Fintype V] in
theorem apexOldPart_card_add_one_of_mem [Finite V]
    (S : Finset (Option (DeletedPair x y))) (h : none ∈ S) :
    (apexOldPart x y S).card + 1 = S.card := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rw [apexOldPart, Finset.card_map, Finset.card_subtype]
  have herase := Finset.card_erase_add_one h
  have hfilter : S.filter (fun z => z ≠ none) = S.erase none := by
    ext z
    simp [and_comm]
  simpa [hfilter] using herase

omit [DecidableEq V] [Fintype V] in
theorem apexOldPart_card_of_not_mem [Finite V]
    (S : Finset (Option (DeletedPair x y))) (h : none ∉ S) :
    (apexOldPart x y S).card = S.card := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rw [apexOldPart, Finset.card_map, Finset.card_subtype]
  have hfilter : S.filter (fun z => z ≠ none) = S := by
    apply Finset.filter_eq_self.mpr
    intro z hz
    rintro rfl
    exact h hz
  rw [hfilter]

/-- Old vertices away from `x,y`, bundled for insertion into the apex graph. -/
abbrev AwayPair (x y : V) := {z : V // z ≠ x ∧ z ≠ y}

def awayPairToApex (x y : V) : AwayPair x y ↪ Option (DeletedPair x y) where
  toFun z := some ⟨z.1, by simp [z.2.1, z.2.2]⟩
  inj' := by
    intro a b h
    change some (⟨a.1, _⟩ : DeletedPair x y) =
      some (⟨b.1, _⟩ : DeletedPair x y) at h
    injection h with hd
    exact Subtype.ext (congrArg (fun d : DeletedPair x y => d.1) hd)

def awayPairFinset (x y : V) (I : Finset V) : Finset (AwayPair x y) :=
  I.subtype (fun z => z ≠ x ∧ z ≠ y)

def apexCompression (x y : V) (I : Finset V) :
    Finset (Option (DeletedPair x y)) :=
  let O := (awayPairFinset x y I).map (awayPairToApex x y)
  if x ∈ I ∨ y ∈ I then insert none O else O

omit [Fintype V] in
@[simp] theorem mem_awayPairFinset [Finite V] {I : Finset V} {z : AwayPair x y} :
    z ∈ awayPairFinset x y I ↔ z.1 ∈ I := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  simp [awayPairFinset]

omit [DecidableRel G.Adj] [Fintype V] in
theorem apexCompression_card [Finite V]
    (hxy : G.Adj x y) (I : Finset V) (hI : G.IsIndepSet I) :
    (apexCompression x y I).card = I.card := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let P : Finset V := {x, y}
  have hsplit := Finset.card_sdiff_add_card_inter I P
  have hawayCard : (awayPairFinset x y I).card = (I \ P).card := by
    simp only [awayPairFinset, Finset.card_subtype]
    congr 1
    ext z
    simp only [Finset.mem_filter, Finset.mem_sdiff, P, Finset.mem_insert,
      Finset.mem_singleton]
    tauto
  have hnone : none ∉ (awayPairFinset x y I).map (awayPairToApex x y) := by
    intro h
    rw [Finset.mem_map] at h
    obtain ⟨a, -, ha⟩ := h
    change some (⟨a.1, _⟩ : DeletedPair x y) = none at ha
    exact Option.some_ne_none _ ha
  by_cases hspecial : x ∈ I ∨ y ∈ I
  · have hinter : (I ∩ P).card = 1 := by
      have hnotboth : ¬ (x ∈ I ∧ y ∈ I) := by
        rintro ⟨hx, hy⟩
        exact hI hx hy hxy.ne hxy
      rcases hspecial with hx | hy
      · have hy : y ∉ I := fun hy => hnotboth ⟨hx, hy⟩
        have : I ∩ P = {x} := by ext z; simp [P, hx, hy]
        simp [this]
      · have hx : x ∉ I := fun hx => hnotboth ⟨hx, hy⟩
        have : I ∩ P = {y} := by ext z; simp [P, hx, hy]
        simp [this]
    rw [apexCompression, if_pos (by assumption), Finset.card_insert_of_not_mem hnone,
      Finset.card_map, hawayCard]
    omega
  · have hx : x ∉ I := fun hx => hspecial (Or.inl hx)
    have hy : y ∉ I := fun hy => hspecial (Or.inr hy)
    have hinter : (I ∩ P).card = 0 := by
      have : I ∩ P = ∅ := by ext z; simp [P, hx, hy]
      simp [this]
    rw [apexCompression, if_neg hspecial, Finset.card_map, hawayCard]
    omega

omit [Fintype V] in
@[simp] theorem none_mem_apexCompression [Finite V] (I : Finset V) :
    none ∈ apexCompression x y I ↔ x ∈ I ∨ y ∈ I := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hnone : none ∉ (awayPairFinset x y I).map (awayPairToApex x y) := by
    intro hm
    rw [Finset.mem_map] at hm
    obtain ⟨a, -, ha⟩ := hm
    change some (⟨a.1, _⟩ : DeletedPair x y) = none at ha
    exact Option.some_ne_none _ ha
  by_cases h : x ∈ I ∨ y ∈ I
  · simp [apexCompression, h, hnone]
  · simp [apexCompression, h, hnone]

omit [Fintype V] in
@[simp] theorem some_mem_apexCompression [Finite V] (I : Finset V) (d : DeletedPair x y) :
    some d ∈ apexCompression x y I ↔ d.1 ∈ I := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  by_cases h : x ∈ I ∨ y ∈ I
  · rw [apexCompression, if_pos h]
    simp only [Finset.mem_insert, Option.some_ne_none, false_or, Finset.mem_map]
    constructor
    · rintro ⟨a, ha, had⟩
      have hav : a.1 = d.1 := by
        change some (⟨a.1, _⟩ : DeletedPair x y) = some d at had
        exact congrArg Subtype.val (Option.some.inj had)
      simpa [hav] using (mem_awayPairFinset.mp ha)
    · intro hdI
      let a : AwayPair x y := ⟨d.1, by
        simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] using d.2⟩
      exact ⟨a, mem_awayPairFinset.mpr hdI, by rfl⟩
  · rw [apexCompression, if_neg h, Finset.mem_map]
    constructor
    · rintro ⟨a, ha, had⟩
      have hav : a.1 = d.1 := by
        change some (⟨a.1, _⟩ : DeletedPair x y) = some d at had
        exact congrArg Subtype.val (Option.some.inj had)
      simpa [hav] using (mem_awayPairFinset.mp ha)
    · intro hdI
      let a : AwayPair x y := ⟨d.1, by
        simpa only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff,
          not_or] using d.2⟩
      exact ⟨a, mem_awayPairFinset.mpr hdI, by rfl⟩

omit [Fintype V] in
theorem apexCompression_subset [Finite V]
    (S : Finset (Option (DeletedPair x y))) (I : Finset V)
    (hIH : I ⊆ insert x (insert y (apexOldPart x y S)))
    (hapex : x ∈ I ∨ y ∈ I → none ∈ S) :
    apexCompression x y I ⊆ S := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  intro q hq
  cases q with
  | none => exact hapex ((none_mem_apexCompression I).mp hq)
  | some d =>
      have hdI : d.1 ∈ I := (some_mem_apexCompression I d).mp hq
      have hdH := hIH hdI
      have hdx : d.1 ≠ x := by
        intro h
        exact d.2 (Or.inl h)
      have hdy : d.1 ≠ y := by
        intro h
        exact d.2 (Or.inr h)
      have hdOld : d.1 ∈ apexOldPart x y S := by
        simpa [hdx, hdy] using hdH
      obtain ⟨e, heS, heq⟩ := mem_apexOldPart.mp hdOld
      have hed : e = d := Subtype.ext heq
      simpa [hed] using heS

omit [DecidableRel G.Adj] [Fintype V] in
theorem apexCompression_indep [Finite V]
    (_hxy : G.Adj x y) (I : Finset V) (hI : G.IsIndepSet I) :
    (commonNeighborApexGraph (G := G) (x := x) (y := y)).IsIndepSet
      (apexCompression x y I) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  intro a ha b hb hab hAdj
  cases a with
  | none =>
      cases b with
      | none => exact hAdj
      | some b =>
          have hspecial := (none_mem_apexCompression I).mp ha
          have hbI := (some_mem_apexCompression I b).mp hb
          rcases hspecial with hxI | hyI
          · exact hI hxI hbI (fun h => b.2 (Or.inl h.symm)) hAdj.1
          · exact hI hyI hbI (fun h => b.2 (Or.inr h.symm)) hAdj.2
  | some a =>
      cases b with
      | none =>
          have haI := (some_mem_apexCompression I a).mp ha
          have hspecial := (none_mem_apexCompression I).mp hb
          rcases hspecial with hxI | hyI
          · exact hI haI hxI (fun h => a.2 (Or.inl h)) hAdj.1.symm
          · exact hI haI hyI (fun h => a.2 (Or.inr h)) hAdj.2.symm
      | some b =>
          have haI := (some_mem_apexCompression I a).mp ha
          have hbI := (some_mem_apexCompression I b).mp hb
          exact hI haI hbI (fun h => hab (congrArg some (Subtype.ext h))) hAdj

omit [DecidableRel G.Adj] [Fintype V] in
/-- Replacing a present apex by the adjacent pair `x,y` does not increase
the independence number. -/
theorem alphaOn_apexReplacement_le [Finite V]
    (hxy : G.Adj x y) (S : Finset (Option (DeletedPair x y)))
    (hapex : none ∈ S) :
    alphaOn G (insert x (insert y (apexOldPart x y S))) ≤
      alphaOn (commonNeighborApexGraph (G := G) (x := x) (y := y)) S := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨I, hIH, hI, hIcard⟩ := exists_maximum_independent_subset G
    (insert x (insert y (apexOldPart x y S)))
  let K := apexCompression x y I
  have hKS : K ⊆ S := apexCompression_subset S I hIH (fun _ => hapex)
  have hKind : (commonNeighborApexGraph (G := G) (x := x) (y := y)).IsIndepSet K :=
    apexCompression_indep hxy I hI
  have hKalpha := card_le_alphaOn hKS hKind
  rw [← hIcard, ← apexCompression_card hxy I hI]
  exact hKalpha

omit [DecidableRel G.Adj] in
/-- A maximizing apex witness cannot contain the apex once `f G ≤ f G0`. -/
theorem apex_not_mem_maximumWitness
    (hxy : G.Adj x y) (S : Finset (Option (DeletedPair x y)))
    (hSf : potential (commonNeighborApexGraph (G := G) (x := x) (y := y)) S =
      f (commonNeighborApexGraph (G := G) (x := x) (y := y)))
    (hf : f G ≤ f (commonNeighborApexGraph (G := G) (x := x) (y := y))) :
    none ∉ S := by
  classical
  intro hapex
  let H := insert x (insert y (apexOldPart x y S))
  have hxOld : x ∉ apexOldPart x y S := by
    rintro hx
    obtain ⟨d, -, hd⟩ := mem_apexOldPart.mp hx
    exact d.2 (Or.inl hd)
  have hyOld : y ∉ apexOldPart x y S := by
    rintro hy
    obtain ⟨d, -, hd⟩ := mem_apexOldPart.mp hy
    exact d.2 (Or.inr hd)
  have hHcard : H.card = S.card + 1 := by
    have hold := apexOldPart_card_add_one_of_mem S hapex
    simp only [H]
    rw [Finset.card_insert_of_not_mem, Finset.card_insert_of_not_mem]
    · omega
    · exact hyOld
    · simp [hxy.ne, hxOld]
  have halpha := alphaOn_apexReplacement_le hxy S hapex
  have hpot := potential_le_f G H
  simp only [Erdos922.potential] at hpot
  rw [hHcard] at hpot
  rw [Erdos922.potential] at hSf
  change alphaOn G H ≤ alphaOn
    (commonNeighborApexGraph (G := G) (x := x) (y := y)) S at halpha
  omega

omit [DecidableEq V] [Fintype V] in
theorem apexOldPart_mono [Finite V] {S T : Finset (Option (DeletedPair x y))}
    (hST : S ⊆ T) : apexOldPart x y S ⊆ apexOldPart x y T := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  intro z hz
  obtain ⟨d, hdS, rfl⟩ := mem_apexOldPart.mp hz
  exact mem_apexOldPart.mpr ⟨d, hST hdS, rfl⟩

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem apexOldPart_indep [Finite V]
    (S : Finset (Option (DeletedPair x y)))
    (hS : (commonNeighborApexGraph (G := G) (x := x) (y := y)).IsIndepSet S) :
    G.IsIndepSet (apexOldPart x y S) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  intro a ha b hb hab hAdj
  obtain ⟨da, hda, rfl⟩ := mem_apexOldPart.mp ha
  obtain ⟨db, hdb, rfl⟩ := mem_apexOldPart.mp hb
  exact hS hda hdb (fun h => hab (congrArg Subtype.val (Option.some.inj h))) hAdj

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
/-- When the apex is absent, the witness and its old-vertex image have equal
independence number. -/
theorem alphaOn_apex_eq_old_of_not_mem [Finite V]
    (hxy : G.Adj x y) (S : Finset (Option (DeletedPair x y)))
    (hno : none ∉ S) :
    alphaOn (commonNeighborApexGraph (G := G) (x := x) (y := y)) S =
      alphaOn G (apexOldPart x y S) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  apply Nat.le_antisymm
  · obtain ⟨K, hKS, hK, hKcard⟩ := exists_maximum_independent_subset
      (commonNeighborApexGraph (G := G) (x := x) (y := y)) S
    have hnoneK : none ∉ K := fun h => hno (hKS h)
    rw [← hKcard, ← apexOldPart_card_of_not_mem K hnoneK]
    exact card_le_alphaOn (apexOldPart_mono hKS) (apexOldPart_indep K hK)
  · obtain ⟨I, hIJ, hI, hIcard⟩ := exists_maximum_independent_subset G
      (apexOldPart x y S)
    have hxJ : x ∉ apexOldPart x y S := by
      rintro hx
      obtain ⟨d, -, hd⟩ := mem_apexOldPart.mp hx
      exact d.2 (Or.inl hd)
    have hyJ : y ∉ apexOldPart x y S := by
      rintro hy
      obtain ⟨d, -, hd⟩ := mem_apexOldPart.mp hy
      exact d.2 (Or.inr hd)
    have hxI : x ∉ I := fun hx => hxJ (hIJ hx)
    have hyI : y ∉ I := fun hy => hyJ (hIJ hy)
    have hsubH : I ⊆ insert x (insert y (apexOldPart x y S)) := by
      intro z hz
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hIJ hz))
    let K := apexCompression x y I
    have hKS : K ⊆ S := apexCompression_subset S I hsubH (by
      rintro (hx | hy)
      · exact (hxI hx).elim
      · exact (hyI hy).elim)
    have hK : (commonNeighborApexGraph (G := G) (x := x) (y := y)).IsIndepSet K :=
      apexCompression_indep hxy I hI
    rw [← hIcard, ← apexCompression_card hxy I hI]
    exact card_le_alphaOn hKS hK

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem potential_apex_eq_old_of_not_mem [Finite V]
    (hxy : G.Adj x y) (S : Finset (Option (DeletedPair x y)))
    (hno : none ∉ S) :
    potential (commonNeighborApexGraph (G := G) (x := x) (y := y)) S =
      potential G (apexOldPart x y S) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rw [potential, potential, apexOldPart_card_of_not_mem S hno,
    alphaOn_apex_eq_old_of_not_mem hxy S hno]

omit [DecidableRel G.Adj] [Fintype V] in
theorem triangleExtension_card [Finite V]
    (hxy : G.Adj x y) (hxt : G.Adj x u) (hyt : G.Adj y u)
    (J : Finset V) (hxJ : x ∉ J) (hyJ : y ∉ J) (htJ : u ∉ J) :
    (insert x (insert y (insert u J))).card = J.card + 3 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have htcard : (insert u J).card = J.card + 1 := Finset.card_insert_of_not_mem htJ
  have hycard : (insert y (insert u J)).card = (insert u J).card + 1 := by
    apply Finset.card_insert_of_not_mem
    simp [hyt.ne, hyJ]
  have hxcard : (insert x (insert y (insert u J))).card =
      (insert y (insert u J)).card + 1 := by
    apply Finset.card_insert_of_not_mem
    simp [hxy.ne, hxt.ne, hxJ]
  omega

omit [DecidableRel G.Adj] [Fintype V] in
theorem alphaOn_triangleExtension_le [Finite V]
    (hxy : G.Adj x y) (hxt : G.Adj x u) (hyt : G.Adj y u)
    (J : Finset V) :
    alphaOn G (insert x (insert y (insert u J))) ≤ alphaOn G J + 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨I, hIH, hI, hIcard⟩ := exists_maximum_independent_subset G
    (insert x (insert y (insert u J)))
  let P : Finset V := {x, y, u}
  let O := I \ P
  have hOJ : O ⊆ J := by
    intro z hz
    have hzI := (Finset.mem_sdiff.mp hz).1
    have hzP := (Finset.mem_sdiff.mp hz).2
    have hzH := hIH hzI
    simp only [Finset.mem_insert] at hzH
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at hzP
    rcases hzH with rfl | rfl | rfl | hz
    · exact (hzP (Or.inl rfl)).elim
    · exact (hzP (Or.inr (Or.inl rfl))).elim
    · exact (hzP (Or.inr (Or.inr rfl))).elim
    · exact hz
  have hOind : G.IsIndepSet O := hI.mono (by intro z hz; exact (Finset.mem_sdiff.mp hz).1)
  have hOalpha : O.card ≤ alphaOn G J := card_le_alphaOn hOJ hOind
  have hinter : (I ∩ P).card ≤ 1 := by
    rw [Finset.card_le_one_iff]
    intro a b ha hb
    obtain ⟨haI, haP⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbI, hbP⟩ := Finset.mem_inter.mp hb
    simp only [P, Finset.mem_insert, Finset.mem_singleton] at haP hbP
    rcases haP with rfl | rfl | rfl <;> rcases hbP with rfl | rfl | rfl
    all_goals try rfl
    all_goals first
      | exact (hI haI hbI hxy.ne hxy).elim
      | exact (hI haI hbI hxy.ne.symm hxy.symm).elim
      | exact (hI haI hbI hxt.ne hxt).elim
      | exact (hI haI hbI hxt.ne.symm hxt.symm).elim
      | exact (hI haI hbI hyt.ne hyt).elim
      | exact (hI haI hbI hyt.ne.symm hyt.symm).elim
  have hsplit := Finset.card_sdiff_add_card_inter I P
  change O.card + (I ∩ P).card = I.card at hsplit
  rw [← hIcard]
  omega

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The no-induced-diamond conclusion for a genuine order-minimal
counterexample: common neighbors of every edge form a clique. -/
theorem commonNeighbors_isClique_of_orderMinimalCounterexample
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G)
    (x y : V) (hxy : G.Adj x y) :
    G.IsClique {z | G.Adj x z ∧ G.Adj y z} := by
  classical
  intro u hu v hv huv
  by_contra huvNA
  have hxu : G.Adj x u := hu.1
  have hyu : G.Adj y u := hu.2
  have hxv : G.Adj x v := hv.1
  have hyv : G.Adj y v := hv.2
  let G0 := commonNeighborApexGraph (G := G) (x := x) (y := y)
  have hfLower : f G ≤ f G0 :=
    f_le_f_apex hmin hxy hxu hyu hxv hyv huv huvNA
  obtain ⟨S, hSf⟩ := exists_maximum_potential G0
  have hno : none ∉ S := apex_not_mem_maximumWitness hxy S hSf hfLower
  let J := apexOldPart x y S
  have hpotTransport := potential_apex_eq_old_of_not_mem hxy S hno
  change potential G0 S = potential G J at hpotTransport
  have hJle := potential_le_f G J
  have hfEq : f G0 = f G := by
    have heq : f G0 = potential G J := hSf.symm.trans hpotTransport
    omega
  have hJmax : potential G J = f G := by
    rw [← hpotTransport, hSf, hfEq]
  have halphaSJ : alphaOn G0 S = alphaOn G J := by
    exact alphaOn_apex_eq_old_of_not_mem hxy S hno
  have hxJ : x ∉ J := by
    rintro hx
    obtain ⟨d, -, hd⟩ := mem_apexOldPart.mp hx
    exact d.2 (Or.inl hd)
  have hyJ : y ∉ J := by
    rintro hy
    obtain ⟨d, -, hd⟩ := mem_apexOldPart.mp hy
    exact d.2 (Or.inr hd)
  -- Adding the apex to a maximizing old witness forces an independent set
  -- one vertex larger, whose old part avoids every common neighbor.
  let K : Finset (Option (DeletedPair x y)) := insert none S
  have hKcard : K.card = S.card + 1 := Finset.card_insert_of_not_mem hno
  have hKpot := potential_le_f G0 K
  rw [← hSf] at hKpot
  have halphaK : alphaOn G0 S + 1 ≤ alphaOn G0 K := by
    simp only [potential, hKcard] at hKpot
    omega
  obtain ⟨L, hLK, hLind, hLcard⟩ := exists_maximum_independent_subset G0 K
  have hnoneL : none ∈ L := by
    by_contra hn
    have hLS : L ⊆ S := by
      intro z hz
      have hzK := hLK hz
      simp only [K, Finset.mem_insert] at hzK
      rcases hzK with rfl | hzS
      · exact (hn hz).elim
      · exact hzS
    have hLle := card_le_alphaOn hLS hLind
    rw [hLcard] at hLle
    omega
  let I := apexOldPart x y L
  have hIcardAdd : I.card + 1 = L.card :=
    apexOldPart_card_add_one_of_mem L hnoneL
  have hIJ : I ⊆ J := by
    intro z hz
    obtain ⟨d, hdL, rfl⟩ := mem_apexOldPart.mp hz
    have hdK := hLK hdL
    simp only [K, Finset.mem_insert] at hdK
    rcases hdK with hnone | hdS
    · exact (Option.some_ne_none d hnone).elim
    · exact mem_apexOldPart.mpr ⟨d, hdS, rfl⟩
  have hIind : G.IsIndepSet I := apexOldPart_indep L hLind
  have hIle : I.card ≤ alphaOn G J := card_le_alphaOn hIJ hIind
  have hIcard : I.card = alphaOn G J := by
    apply Nat.le_antisymm hIle
    rw [← halphaSJ]
    rw [hLcard] at hIcardAdd
    omega
  let A := commonNeighborFinset G x y
  have hIA : Disjoint I A := by
    rw [Finset.disjoint_left]
    intro z hzI hzA
    obtain ⟨d, hdL, rfl⟩ := mem_apexOldPart.mp hzI
    have hdcommon := mem_commonNeighborFinset.mp hzA
    exact hLind hnoneL hdL (by simp) hdcommon
  have hIU : I ⊆ J \ A := by
    intro z hz
    exact Finset.mem_sdiff.mpr ⟨hIJ hz, Finset.disjoint_left.mp hIA hz⟩
  have halphaU : alphaOn G (J \ A) = alphaOn G J := by
    apply Nat.le_antisymm
    · exact alphaOn_mono (Finset.sdiff_subset)
    · rw [← hIcard]
      exact card_le_alphaOn hIU hIind
  -- Every common neighbor must already occur in the maximizing witness.
  have hAJ : A ⊆ J := by
    intro t htA
    by_contra htJ
    have ht := mem_commonNeighborFinset.mp htA
    let H := insert x (insert y (insert t J))
    have hHcard := triangleExtension_card hxy ht.1 ht.2 J hxJ hyJ htJ
    have halphaH := alphaOn_triangleExtension_le hxy ht.1 ht.2 J
    have hpotH := potential_le_f G H
    rw [← hJmax] at hpotH
    simp only [potential] at hpotH
    change H.card = J.card + 3 at hHcard
    change alphaOn G H ≤ alphaOn G J + 1 at halphaH
    omega
  -- The common-neighbor lower bound makes `J \ A` smaller than twice its
  -- independence number, exactly the Hajnal hypothesis.
  have hcommon := chi_sub_two_lt_commonNeighbors
    hmin hxy hxu hyu hxv hyv huv huvNA
  have hAcard : A.card = Nat.card (CommonNeighbor G x y) := by
    letI : Fintype (CommonNeighbor G x y) := Fintype.ofFinite _
    let e : CommonNeighbor G x y ≃ {z : V // z ∈ A} := {
      toFun := fun z => ⟨z.1, (mem_commonNeighborFinset).mpr z.2⟩
      invFun := fun z => ⟨z.1, (mem_commonNeighborFinset).mp z.2⟩
      left_inv := fun z => Subtype.ext rfl
      right_inv := fun z => Subtype.ext rfl }
    rw [Nat.card_eq_fintype_card, Fintype.card_congr e, Fintype.card_coe]
  have hgap := Erdos922FullB.counterexample_gap_int G hmin.counterexample
  change f G + 2 < (Erdos922FullB.chiNat G : ℤ) at hgap
  have hA_le_J : A.card ≤ J.card := Finset.card_le_card hAJ
  have hdiff : (J \ A).card = J.card - A.card := Finset.card_sdiff hAJ
  have hlarge : (J \ A).card < 2 * alphaOn G (J \ A) := by
    have hJmaxInt := hJmax
    change (J.card : ℤ) - 2 * (alphaOn G J : ℤ) = f G at hJmaxInt
    rw [halphaU, hdiff, hAcard]
    omega
  exact hajnal_apexWitness_contradiction G x y J hxy hxJ hyJ
    (by simpa [A] using halphaU) (by simpa [A] using hlarge) hJmax

end MinimalCounterexampleDiamond

end Erdos922Diamond
