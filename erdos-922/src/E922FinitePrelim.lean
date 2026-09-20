/-
Lean 4.19 compatibility adaptation of the credited public Folkman proof.
Original mathematics: Jon Folkman. Original formal authors: Codex; GPT-5.6 Sol.
plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos922.lean, original lines396--807.
+This is a preliminary proof segment, not the complete finite Folkman supplier.
Local compatibility work under Gott-L's direction with Codex assistance.
No claim of a new mathematical result or priority. See PROVENANCE.md.
-/
import E922FiniteBase
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Copy

open SimpleGraph
open scoped ENat

namespace Erdos922FullB

universe u

/-!
This file develops the numerical core of the minimal-counterexample argument
for Folkman's theorem.  The maximum is localized to an ambient vertex
finset.  This makes the split inequality independent of any equivalences
between nested subtype vertex types.
-/

/-- The maximum size of an independent subset of `S`. -/
noncomputable def alphaOn {V : Type u} (G : SimpleGraph V) (S : Finset V) : ℕ := by
  classical
  exact Nat.findGreatest
    (fun n ↦ ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet I ∧ I.card = n) S.card

theorem exists_maximum_independent_subset {V : Type u}
    (G : SimpleGraph V) (S : Finset V) :
    ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet I ∧ I.card = alphaOn G S := by
  classical
  unfold alphaOn
  let P : ℕ → Prop := fun n ↦
    ∃ I : Finset V, I ⊆ S ∧ G.IsIndepSet I ∧ I.card = n
  change P (Nat.findGreatest P S.card)
  apply Nat.findGreatest_spec (m := 0) (Nat.zero_le S.card)
  exact ⟨(∅ : Finset V), by simp⟩

theorem card_le_alphaOn {V : Type u} {G : SimpleGraph V}
    {I S : Finset V} (hIS : I ⊆ S) (hI : G.IsIndepSet I) :
    I.card ≤ alphaOn G S := by
  classical
  unfold alphaOn
  exact Nat.le_findGreatest (Finset.card_le_card hIS) ⟨I, hIS, hI, rfl⟩

theorem alphaOn_le_card {V : Type u} (G : SimpleGraph V) (S : Finset V) :
    alphaOn G S ≤ S.card := by
  classical
  unfold alphaOn
  exact Nat.findGreatest_le _

@[simp] theorem alphaOn_empty {V : Type u} (G : SimpleGraph V) :
    alphaOn G ∅ = 0 := by
  exact Nat.le_zero.mp (by simpa using alphaOn_le_card G ∅)

/-- The signed deficiency `|S| - 2 α(G[S])`. -/
noncomputable def potential {V : Type u} (G : SimpleGraph V) (S : Finset V) : ℤ :=
  (S.card : ℤ) - 2 * (alphaOn G S : ℤ)

@[simp] theorem potential_empty {V : Type u} (G : SimpleGraph V) :
    potential G ∅ = 0 := by
  simp [potential]

/-- The canonical embedding of the vertex type of a finset-induced graph. -/
def subtypeEmbedding {V : Type u} (S : Finset V) : {v : V // v ∈ S} ↪ V :=
  ⟨Subtype.val, Subtype.val_injective⟩

@[simp] theorem subtypeEmbedding_apply {V : Type u} (S : Finset V)
    (v : {v : V // v ∈ S}) : subtypeEmbedding S v = v.1 := rfl

/-- Independence number transport through the canonical embedding of an
induced vertex finset. -/
theorem alphaOn_induce_eq_alphaOn_map
    {V : Type u} (G : SimpleGraph V) (S : Finset V)
    (A : Finset {v : V // v ∈ S}) :
    alphaOn (G.induce (S : Set V)) A =
      alphaOn G (A.map (subtypeEmbedding S)) := by
  classical
  apply Nat.le_antisymm
  · obtain ⟨I, hIA, hIind, hIcard⟩ :=
      exists_maximum_independent_subset (G.induce (S : Set V)) A
    rw [← hIcard]
    have hmap_ind : G.IsIndepSet (I.map (subtypeEmbedding S)) := by
      intro x hx y hy hxy hadj
      change x ∈ I.map (subtypeEmbedding S) at hx
      change y ∈ I.map (subtypeEmbedding S) at hy
      rw [Finset.mem_map] at hx hy
      obtain ⟨x', hx'I, rfl⟩ := hx
      obtain ⟨y', hy'I, rfl⟩ := hy
      exact hIind hx'I hy'I (fun h ↦ hxy (congrArg Subtype.val h)) hadj
    have hle := card_le_alphaOn
      ((Finset.map_subset_map (f := subtypeEmbedding S)).mpr hIA) hmap_ind
    simpa using hle
  · obtain ⟨J, hJA, hJind, hJcard⟩ :=
      exists_maximum_independent_subset G (A.map (subtypeEmbedding S))
    obtain ⟨I, hIA, rfl⟩ := Finset.subset_map_iff.mp hJA
    rw [← hJcard, Finset.card_map]
    apply card_le_alphaOn hIA
    intro x hx y hy hxy hadj
    apply hJind
    · exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
    · exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
    · exact fun h ↦ hxy (Subtype.ext h)
    · exact hadj

/-- Signed potential is invariant under the canonical embedding of an
induced vertex finset. -/
theorem potential_induce_eq_potential_map
    {V : Type u} (G : SimpleGraph V) (S : Finset V)
    (A : Finset {v : V // v ∈ S}) :
    potential (G.induce (S : Set V)) A =
      potential G (A.map (subtypeEmbedding S)) := by
  classical
  rw [potential, potential, alphaOn_induce_eq_alphaOn_map, Finset.card_map]

@[simp] theorem univ_map_subtypeEmbedding
    {V : Type u} (S : Finset V) :
    (Finset.univ : Finset {v : V // v ∈ S}).map (subtypeEmbedding S) = S := by
  classical
  ext v
  simp [subtypeEmbedding]

/-- Maximum signed deficiency among vertex subsets of `U`.  The empty set is
among the candidates, so this maximum is always nonnegative. -/
noncomputable def fOn {V : Type u} (G : SimpleGraph V) (U : Finset V) : ℤ := by
  classical
  exact (U.powerset.image (potential G)).max'
    (U.powerset_nonempty.image (potential G))

theorem exists_maximum_potential_on {V : Type u} (G : SimpleGraph V) (U : Finset V) :
    ∃ S : Finset V, S ⊆ U ∧ potential G S = fOn G U := by
  classical
  let P : Finset ℤ := U.powerset.image (potential G)
  have hP : P.Nonempty := U.powerset_nonempty.image (potential G)
  have hm : P.max' hP ∈ P := P.max'_mem hP
  obtain ⟨S, hSU, hpot⟩ := Finset.mem_image.mp hm
  refine ⟨S, by simpa using hSU, ?_⟩
  have hf : fOn G U = P.max' hP := by simp only [fOn, P]
  exact hpot.trans hf.symm

theorem potential_le_fOn {V : Type u} (G : SimpleGraph V)
    {S U : Finset V} (hSU : S ⊆ U) : potential G S ≤ fOn G U := by
  classical
  let P : Finset ℤ := U.powerset.image (potential G)
  have hmem : potential G S ∈ P := by
    apply Finset.mem_image.mpr
    exact ⟨S, Finset.mem_powerset.mpr hSU, rfl⟩
  have hle : potential G S ≤ P.max' ⟨potential G S, hmem⟩ := P.le_max' _ hmem
  simpa only [fOn, P] using hle

/-- The localized maximum on `S` is definitionally the global maximum for
the graph induced on `S`, after transporting subtype finsets. -/
theorem fOn_induce_univ_eq_fOn
    {V : Type u} (G : SimpleGraph V) (S : Finset V) :
    fOn (G.induce (S : Set V))
        (Finset.univ : Finset {v : V // v ∈ S}) = fOn G S := by
  classical
  apply le_antisymm
  · obtain ⟨A, hAuniv, hAf⟩ := exists_maximum_potential_on
      (G.induce (S : Set V)) (Finset.univ : Finset {v : V // v ∈ S})
    rw [← hAf, potential_induce_eq_potential_map]
    apply potential_le_fOn G
    have hmap := (Finset.map_subset_map (f := subtypeEmbedding S)).mpr hAuniv
    simpa only [univ_map_subtypeEmbedding] using hmap
  · obtain ⟨B, hBS, hBf⟩ := exists_maximum_potential_on G S
    have hBmap : B ⊆
        (Finset.univ : Finset {v : V // v ∈ S}).map (subtypeEmbedding S) := by
      simpa only [univ_map_subtypeEmbedding] using hBS
    obtain ⟨A, hAuniv, hBA⟩ := Finset.subset_map_iff.mp hBmap
    rw [← hBf, hBA, ← potential_induce_eq_potential_map]
    exact potential_le_fOn (G.induce (S : Set V)) hAuniv

/-- An independent set in a cycle graph occupies at most half of its
vertices.  The shift by one injects it into its complement. -/
theorem twice_card_le_of_cycleGraph_isIndepSet
    {n : ℕ} (hn : 3 ≤ n) {A : Finset (Fin n)}
    (hA : (SimpleGraph.cycleGraph n).IsIndepSet A) : 2 * A.card ≤ n := by
  classical
  have hnzero : NeZero n := ⟨by omega⟩
  let shift : Fin n ↪ Fin n := (Equiv.addRight (1 : Fin n)).toEmbedding
  have hadj (i : Fin n) : (SimpleGraph.cycleGraph n).Adj i (shift i) := by
    rw [SimpleGraph.cycleGraph_adj']
    right
    simp [shift, Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hsub : A.map shift ⊆ Aᶜ := by
    intro j hj
    rw [Finset.mem_map] at hj
    obtain ⟨i, hi, rfl⟩ := hj
    rw [Finset.mem_compl]
    intro hshift
    exact hA hi hshift (hadj i).ne (hadj i)
  have hc := Finset.card_le_card hsub
  simp only [Finset.card_map, Finset.card_compl, Fintype.card_fin] at hc
  omega

/-- Any embedded odd cycle certifies strictly positive hereditary
deficiency. -/
theorem fOn_pos_of_odd_cycle_copy
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (c : SimpleGraph.Copy (SimpleGraph.cycleGraph n) G) :
    0 < fOn G Finset.univ := by
  classical
  let e : Fin n ↪ V := c.toEmbedding
  let S : Finset V := (Finset.univ : Finset (Fin n)).map e
  have hScard : S.card = n := by simp [S]
  have halpha : 2 * alphaOn G S ≤ n := by
    obtain ⟨J, hJS, hJind, hJcard⟩ := exists_maximum_independent_subset G S
    have hJmap : J ⊆ (Finset.univ : Finset (Fin n)).map e := by simpa [S] using hJS
    obtain ⟨A, hAuniv, hJA⟩ := Finset.subset_map_iff.mp hJmap
    have hAind : (SimpleGraph.cycleGraph n).IsIndepSet A := by
      intro x hx y hy hxy hadj
      apply hJind
      · rw [hJA]
        exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
      · rw [hJA]
        exact Finset.mem_map.mpr ⟨y, hy, rfl⟩
      · exact fun h ↦ hxy (c.injective h)
      · exact c.toHom.map_rel hadj
    have hcycle := twice_card_le_of_cycleGraph_isIndepSet hn hAind
    rw [← hJcard, hJA, Finset.card_map]
    exact hcycle
  have hpot : 0 < potential G S := by
    rw [potential, hScard]
    obtain ⟨m, hm⟩ := hodd
    omega
  exact hpot.trans_le (potential_le_fOn G (Finset.subset_univ S))

theorem fOn_nonneg {V : Type u} (G : SimpleGraph V) (U : Finset V) :
    0 ≤ fOn G U := by
  simpa using potential_le_fOn G (S := (∅ : Finset V)) (Finset.empty_subset U)

theorem ofNat_toNat_fOn {V : Type u} (G : SimpleGraph V) (U : Finset V) :
    (Int.toNat (fOn G U) : ℤ) = fOn G U := by
  exact Int.toNat_of_nonneg (fOn_nonneg G U)

/-- An independent set in a disjoint union splits into independent sets in
the two sides. -/
theorem alphaOn_union_le_add {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {S T : Finset V} (hST : Disjoint S T) :
    alphaOn G (S ∪ T) ≤ alphaOn G S + alphaOn G T := by
  classical
  obtain ⟨I, hI_sub, hI_ind, hI_card⟩ :=
    exists_maximum_independent_subset G (S ∪ T)
  let IS : Finset V := I ∩ S
  let IT : Finset V := I ∩ T
  have hIS_sub : IS ⊆ S := by
    intro x hx
    exact (Finset.mem_inter.mp hx).2
  have hIT_sub : IT ⊆ T := by
    intro x hx
    exact (Finset.mem_inter.mp hx).2
  have hIS_ind : G.IsIndepSet IS := hI_ind.mono (by
    intro x hx
    exact (Finset.mem_inter.mp hx).1)
  have hIT_ind : G.IsIndepSet IT := hI_ind.mono (by
    intro x hx
    exact (Finset.mem_inter.mp hx).1)
  have hparts : IS ∪ IT = I := by
    ext x
    simp only [IS, IT, Finset.mem_union, Finset.mem_inter]
    constructor
    · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
    · intro hx
      have hxST := hI_sub hx
      rcases Finset.mem_union.mp hxST with hxS | hxT
      · exact Or.inl ⟨hx, hxS⟩
      · exact Or.inr ⟨hx, hxT⟩
  have hparts_disj : Disjoint IS IT := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxT
    exact Finset.disjoint_left.mp hST
      (Finset.mem_inter.mp hxS).2 (Finset.mem_inter.mp hxT).2
  have hcard_parts : I.card = IS.card + IT.card := by
    rw [← hparts, Finset.card_union_of_disjoint hparts_disj]
  have hIS_le : IS.card ≤ alphaOn G S := card_le_alphaOn hIS_sub hIS_ind
  have hIT_le : IT.card ≤ alphaOn G T := card_le_alphaOn hIT_sub hIT_ind
  omega

/-- Signed deficiencies are superadditive on disjoint vertex sets. -/
theorem potential_add_le_union {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {S T : Finset V} (hST : Disjoint S T) :
    potential G S + potential G T ≤ potential G (S ∪ T) := by
  have ha := alphaOn_union_le_add (G := G) hST
  have hc := Finset.card_union_of_disjoint hST
  simp only [potential]
  omega

/-- The key potential inequality used in Folkman's split argument. -/
theorem fOn_add_le_fOn_union {V : Type u} [DecidableEq V] (G : SimpleGraph V)
    {U W : Finset V} (hUW : Disjoint U W) :
    fOn G U + fOn G W ≤ fOn G (U ∪ W) := by
  classical
  obtain ⟨S, hSU, hSf⟩ := exists_maximum_potential_on G U
  obtain ⟨T, hTW, hTf⟩ := exists_maximum_potential_on G W
  have hST : Disjoint S T := hUW.mono hSU hTW
  have hsub : S ∪ T ⊆ U ∪ W := Finset.union_subset_union hSU hTW
  rw [← hSf, ← hTf]
  exact (potential_add_le_union hST).trans (potential_le_fOn G hsub)

/-- The natural-valued chromatic number of a finite graph.  This agrees with
the finite value of Mathlib's `ℕ∞`-valued chromatic number. -/
noncomputable def chiNat {V : Type u} (G : SimpleGraph V) : ℕ :=
  ENat.toNat G.chromaticNumber

theorem chromaticNumber_eq_natCast_chiNat {V : Type u} [Finite V]
    (G : SimpleGraph V) : G.chromaticNumber = (chiNat G : ℕ∞) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hne : G.chromaticNumber ≠ ⊤ := by
    have hlt : G.chromaticNumber < ⊤ :=
      G.colorable_of_fintype.chromaticNumber_le.trans_lt (ENat.coe_lt_top _)
    exact hlt.ne
  exact (ENat.coe_toNat hne).symm

theorem colorable_iff_chiNat_le {V : Type u} [Finite V]
    (G : SimpleGraph V) (q : ℕ) : G.Colorable q ↔ chiNat G ≤ q := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rw [← chromaticNumber_le_iff_colorable,
    chromaticNumber_eq_natCast_chiNat G]
  exact ENat.coe_le_coe

theorem colorable_chiNat {V : Type u} [Finite V] (G : SimpleGraph V) :
    G.Colorable (chiNat G) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  exact (colorable_iff_chiNat_le G _).mpr le_rfl

/-- The global form of Folkman's bound, with the signed deficiency maximum
`fOn G univ`; the paper's potential maximum is this number plus two. -/
noncomputable def FolkmanBound {V : Type u} [Fintype V]
    (G : SimpleGraph V) : Prop :=
  G.Colorable (Int.toNat (fOn G Finset.univ) + 2)

theorem folkmanBound_iff_chiNat_le {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    FolkmanBound G ↔ chiNat G ≤ Int.toNat (fOn G Finset.univ) + 2 := by
  exact colorable_iff_chiNat_le G _

theorem not_folkmanBound_iff_lt_chiNat {V : Type u} [Fintype V]
    (G : SimpleGraph V) :
    ¬ FolkmanBound G ↔ Int.toNat (fOn G Finset.univ) + 2 < chiNat G := by
  rw [folkmanBound_iff_chiNat_le]
  omega

theorem counterexample_gap_int {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hG : ¬ FolkmanBound G) :
    fOn G Finset.univ + 2 < (chiNat G : ℤ) := by
  have h := (not_folkmanBound_iff_lt_chiNat G).mp hG
  have hf := ofNat_toNat_fOn G (Finset.univ : Finset V)
  omega

theorem three_le_chiNat_of_not_folkmanBound {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hG : ¬ FolkmanBound G) : 3 ≤ chiNat G := by
  have h := (not_folkmanBound_iff_lt_chiNat G).mp hG
  omega

theorem four_le_chiNat_of_not_folkmanBound_of_fOn_pos
    {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hG : ¬ FolkmanBound G) (hf : 0 < fOn G Finset.univ) :
    4 ≤ chiNat G := by
  have h := (not_folkmanBound_iff_lt_chiNat G).mp hG
  have hcast := ofNat_toNat_fOn G (Finset.univ : Finset V)
  have : 1 ≤ Int.toNat (fOn G Finset.univ) := by omega
  omega

/-- A counterexample minimal by vertex count.  The second conjunct is the
strong-induction hypothesis on *all* smaller finite graph vertex types, so it
also applies to contractions and apex constructions, not only induced
subgraphs. -/
noncomputable def IsOrderMinimalCounterexample
    {V : Type u} [Fintype V] (G : SimpleGraph V) : Prop :=
  ¬ FolkmanBound G ∧
    ∀ {W : Type u} [Fintype W] [DecidableEq W] (H : SimpleGraph W),
      Fintype.card W < Fintype.card V → FolkmanBound H

theorem IsOrderMinimalCounterexample.counterexample
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) : ¬ FolkmanBound G := hG.1

theorem IsOrderMinimalCounterexample.smaller
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G)
    {W : Type u} [Fintype W] (H : SimpleGraph W)
    (hcard : Fintype.card W < Fintype.card V) : FolkmanBound H := by
  classical
  exact hG.2 H hcard

theorem IsOrderMinimalCounterexample.proper_induce
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) (S : Finset V)
    (hS : S ⊂ (Finset.univ : Finset V)) :
    FolkmanBound (G.induce (S : Set V)) := by
  classical
  apply hG.smaller
  have hcard : S.card < Fintype.card V := by
    simpa using Finset.card_lt_card hS
  simpa using hcard

theorem IsOrderMinimalCounterexample.proper_induce_chiNat_le
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) (S : Finset V)
    (hS : S ⊂ (Finset.univ : Finset V)) :
    (chiNat (G.induce (S : Set V)) : ℤ) ≤ fOn G S + 2 := by
  classical
  have hc := (folkmanBound_iff_chiNat_le (G.induce (S : Set V))).mp
    (hG.proper_induce S hS)
  rw [fOn_induce_univ_eq_fOn] at hc
  have hf := ofNat_toNat_fOn G S
  omega

/-- A counterexample to Folkman's bound cannot be two-colorable.  This is
already true before using order minimality: the target number of colors is
at least two because `fOn` is nonnegative. -/
theorem IsOrderMinimalCounterexample.not_colorable_two
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) : ¬ G.Colorable 2 := by
  intro htwo
  apply hG.counterexample
  exact htwo.mono (by omega)

end Erdos922FullB
