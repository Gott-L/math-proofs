/-
Inherited Folkman/Erdos922 finite-proof segment, original lines1038--1615.
Source: plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos922.lean; SHA256
0bc22004ecbe76ab3cc3f263c29c76994b39017828ea835d987139fa324b9971.
Original mathematics: Jon Folkman. Original formal authors: Codex; GPT-5.6 Sol.
Local Lean4.19 port under Gott-L's direction, with Codex/B implementation.
Private compatibility experiment; upstream fixed license remains unverified.
No new mathematical discovery or completed Folkman supplier is claimed.
-/
import E922MapCompat

open SimpleGraph
open scoped ENat


open Function

namespace Erdos922EvenHole

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The preliminary contraction map.  Vertices in `A` go to the left new
vertex, vertices in `B` go to the right new vertex, and all other vertices
retain their name. -/
def preContract (A B : Finset V) (v : V) : V ⊕ Bool :=
  if v ∈ A then .inr false else if v ∈ B then .inr true else .inl v

/-- The actual contracted vertex type.  Taking the range is important: it
removes the unused copies `Sum.inl v` for `v ∈ A ∪ B`. -/
abbrev ContractVertex (A B : Finset V) := Set.range (preContract A B)

/-- The surjection from the old vertex type to the contracted vertex type. -/
def contract (A B : Finset V) (v : V) : ContractVertex A B :=
  ⟨preContract A B v, Set.mem_range_self v⟩

/-- Push all old edges through the contraction. `mapFunctionCompat` deletes
the loops produced inside a contracted fiber. -/
def contractGraph (G : SimpleGraph V) (A B : Finset V) :
    SimpleGraph (ContractVertex A B) :=
  G.mapFunctionCompat (contract A B)

omit [Fintype V] in
theorem preContract_eq_inr_false_iff [Finite V] (A B : Finset V) (v : V) :
    preContract A B v = Sum.inr false ↔ v ∈ A := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  simp only [preContract]
  by_cases hvA : v ∈ A
  · simp [hvA]
  · by_cases hvB : v ∈ B <;> simp [hvA, hvB]

omit [Fintype V] in
theorem preContract_eq_inr_true_iff [Finite V] (A B : Finset V) (hAB : Disjoint A B) (v : V) :
    preContract A B v = Sum.inr true ↔ v ∈ B := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  simp only [preContract]
  by_cases hvA : v ∈ A
  · have hvB : v ∉ B := fun hvB ↦ Finset.disjoint_left.mp hAB hvA hvB
    simp [hvA, hvB]
  · by_cases hvB : v ∈ B <;> simp [hvA, hvB]

omit [Fintype V] in
theorem preContract_eq_inl_iff [Finite V] (A B : Finset V) (v w : V) :
    preContract A B v = Sum.inl w ↔ v = w ∧ w ∉ A ∧ w ∉ B := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  by_cases hvA : v ∈ A
  · constructor
    · intro h
      simp [preContract, hvA] at h
    · rintro ⟨rfl, hnot, -⟩
      exact (hnot hvA).elim
  · by_cases hvB : v ∈ B
    · constructor
      · intro h
        simp [preContract, hvA, hvB] at h
      · rintro ⟨rfl, -, hnot⟩
        exact (hnot hvB).elim
    · constructor
      · intro h
        have hvw : v = w := by simpa [preContract, hvA, hvB] using h
        subst w
        exact ⟨rfl, hvA, hvB⟩
      · rintro ⟨rfl, -, -⟩
        simp [preContract, hvA, hvB]

omit [Fintype V] in
theorem contract_injective_outside [Finite V] (A B : Finset V) {v w : V}
    (hvA : v ∉ A) (hvB : v ∉ B) (hwA : w ∉ A) (hwB : w ∉ B)
    (h : contract A B v = contract A B w) : v = w := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hval := congrArg Subtype.val h
  simpa [contract, preContract, hvA, hvB, hwA, hwB] using hval

omit [Fintype V] in
theorem contract_eq_iff_of_outside [Finite V] (A B : Finset V) {v w : V}
    (hvA : v ∉ A) (hvB : v ∉ B) (hwA : w ∉ A) (hwB : w ∉ B) :
    contract A B v = contract A B w ↔ v = w := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  constructor
  · exact contract_injective_outside A B hvA hvB hwA hwB
  · exact congrArg _

omit [Fintype V] in
theorem contract_eq_of_mem_left [Finite V] (A B : Finset V) {v w : V}
    (hv : v ∈ A) (hw : w ∈ A) : contract A B v = contract A B w := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  apply Subtype.ext
  simp [contract, preContract, hv, hw]

omit [Fintype V] in
theorem contract_eq_of_mem_right [Finite V] (A B : Finset V) (hAB : Disjoint A B) {v w : V}
    (hv : v ∈ B) (hw : w ∈ B) : contract A B v = contract A B w := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hvA : v ∉ A := fun ha ↦ Finset.disjoint_left.mp hAB ha hv
  have hwA : w ∉ A := fun ha ↦ Finset.disjoint_left.mp hAB ha hw
  apply Subtype.ext
  simp [contract, preContract, hvA, hwA, hv, hw]

omit [Fintype V] in
theorem contract_ne_left_right [Finite V] (A B : Finset V) (hAB : Disjoint A B)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) :
    contract A B a ≠ contract A B b := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hbA : b ∉ A := fun hba ↦ Finset.disjoint_left.mp hAB hba hb
  intro h
  have hval := congrArg Subtype.val h
  simp [contract, preContract, ha, hbA, hb] at hval

section Fibers

variable {W : Type*} [DecidableEq W]

omit [DecidableEq V] [DecidableEq W] [Fintype V] in
/-- An independent set descends through a possibly noninjective graph map as
soon as it contains the whole fiber above every image vertex retained.  This
is the key fact that makes the contraction proof honest: retaining only one
old representative of a contracted vertex would not suffice. -/
theorem isIndepSet_map_of_fiber_subset [Finite V] (G : SimpleGraph V) (q : V → W)
    {I : Finset V} {J : Finset W} (hI : G.IsIndepSet I)
    (hfiber : ∀ x ∈ J, ∀ v, q v = x → v ∈ I) :
    (G.mapFunctionCompat q).IsIndepSet J := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rw [SimpleGraph.isIndepSet_iff]
  rintro x hx y hy hxy hAdj
  rcases hAdj with ⟨hqne, u, v, huv, hu, hv⟩
  apply hI (hfiber x hx u hu) (hfiber y hy v hv)
  · intro huvEq
    subst v
    exact hqne (hu.symm.trans hv)
  · exact huv

end Fibers

/-- The vertices of `I` outside the two contracted fibers. -/
def outsidePart (A B I : Finset V) : Finset V :=
  I.filter fun v ↦ v ∉ A ∧ v ∉ B

/-- The image of the outside portion of `I` in the contracted graph. -/
def outsideImage (A B I : Finset V) : Finset (ContractVertex A B) :=
  (outsidePart A B I).image (contract A B)

omit [Fintype V] in
theorem mem_outsidePart_iff [Finite V] (A B I : Finset V) (v : V) :
    v ∈ outsidePart A B I ↔ v ∈ I ∧ v ∉ A ∧ v ∉ B := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  simp [outsidePart]

omit [Fintype V] in
theorem outsideImage_fiber_subset [Finite V] (A B I : Finset V) :
    ∀ x ∈ outsideImage A B I, ∀ v, contract A B v = x → v ∈ I := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  intro x hx v hvx
  simp only [outsideImage, Finset.mem_image] at hx
  rcases hx with ⟨w, hw, rfl⟩
  have hw' := (mem_outsidePart_iff A B I w).mp hw
  have hpw : preContract A B w = Sum.inl w := by
    simp [preContract, hw'.2.1, hw'.2.2]
  have hpv : preContract A B v = Sum.inl w := by
    have := congrArg Subtype.val hvx
    exact this.trans hpw
  have hvw := (preContract_eq_inl_iff A B v w).mp hpv |>.1
  simpa [hvw] using hw'.1

omit [Fintype V] in
theorem isIndepSet_outsideImage [Finite V] (G : SimpleGraph V) (A B I : Finset V)
    (hI : G.IsIndepSet I) :
    (contractGraph G A B).IsIndepSet (outsideImage A B I) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  exact isIndepSet_map_of_fiber_subset G (contract A B) hI
    (outsideImage_fiber_subset A B I)

omit [Fintype V] in
/-- If `I` contains all of `A`, its outside image together with the left
contracted vertex is independent. -/
theorem isIndepSet_insert_left [Finite V] (G : SimpleGraph V) (A B I : Finset V)
    {a : V} (ha : a ∈ A) (hAI : A ⊆ I) (hI : G.IsIndepSet I) :
    (contractGraph G A B).IsIndepSet
      ((insert (contract A B a) (outsideImage A B I) :
        Finset (ContractVertex A B)) : Set (ContractVertex A B)) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  apply isIndepSet_map_of_fiber_subset G (contract A B) hI
  intro x hx v hvx
  simp only [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · apply hAI
    apply (preContract_eq_inr_false_iff A B v).mp
    have hval := congrArg Subtype.val hvx
    simpa [contract, preContract, ha] using hval
  · exact outsideImage_fiber_subset A B I x hx v hvx

omit [Fintype V] in
/-- If `I` contains all of `B`, its outside image together with the right
contracted vertex is independent. -/
theorem isIndepSet_insert_right [Finite V] (G : SimpleGraph V) (A B I : Finset V)
    (hAB : Disjoint A B) {b : V} (hb : b ∈ B) (hBI : B ⊆ I)
    (hI : G.IsIndepSet I) :
    (contractGraph G A B).IsIndepSet
      ((insert (contract A B b) (outsideImage A B I) :
        Finset (ContractVertex A B)) : Set (ContractVertex A B)) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  apply isIndepSet_map_of_fiber_subset G (contract A B) hI
  intro x hx v hvx
  simp only [Finset.mem_insert] at hx
  rcases hx with rfl | hx
  · apply hBI
    apply (preContract_eq_inr_true_iff A B hAB v).mp
    have hbA : b ∉ A := fun hba ↦ Finset.disjoint_left.mp hAB hba hb
    have hval := congrArg Subtype.val hvx
    simpa [contract, preContract, hbA, hb] using hval
  · exact outsideImage_fiber_subset A B I x hx v hvx

omit [Fintype V] in
/-- If `I` contains both full fibers, both contracted vertices can be kept. -/
theorem isIndepSet_insert_both [Finite V] (G : SimpleGraph V) (A B I : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (hAI : A ⊆ I) (hBI : B ⊆ I) (hI : G.IsIndepSet I) :
    (contractGraph G A B).IsIndepSet
      ((insert (contract A B a)
        (insert (contract A B b) (outsideImage A B I)) :
          Finset (ContractVertex A B)) : Set (ContractVertex A B)) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  apply isIndepSet_map_of_fiber_subset G (contract A B) hI
  intro x hx v hvx
  simp only [Finset.mem_insert] at hx
  rcases hx with rfl | rfl | hx
  · apply hAI
    apply (preContract_eq_inr_false_iff A B v).mp
    have hval := congrArg Subtype.val hvx
    simpa [contract, preContract, ha] using hval
  · apply hBI
    apply (preContract_eq_inr_true_iff A B hAB v).mp
    have hbA : b ∉ A := fun hba ↦ Finset.disjoint_left.mp hAB hba hb
    have hval := congrArg Subtype.val hvx
    simpa [contract, preContract, hbA, hb] using hval
  · exact outsideImage_fiber_subset A B I x hx v hvx

section Cardinalities

omit [Fintype V] in
theorem outsideImage_card [Finite V] (A B I : Finset V) :
    (outsideImage A B I).card = (outsidePart A B I).card := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rw [outsideImage, Finset.card_image_iff]
  intro v hv w hw hvw
  have hv' := (mem_outsidePart_iff A B I v).mp hv
  have hw' := (mem_outsidePart_iff A B I w).mp hw
  exact contract_injective_outside A B hv'.2.1 hv'.2.2 hw'.2.1 hw'.2.2 hvw

omit [Fintype V] in
theorem contract_left_not_mem_outsideImage [Finite V] (A B I : Finset V) {a : V} (ha : a ∈ A) :
    contract A B a ∉ outsideImage A B I := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  intro h
  simp only [outsideImage, Finset.mem_image] at h
  rcases h with ⟨v, hv, hva⟩
  have hv' := (mem_outsidePart_iff A B I v).mp hv
  have hval := congrArg Subtype.val hva
  simp [contract, preContract, ha, hv'.2.1, hv'.2.2] at hval

omit [Fintype V] in
theorem contract_right_not_mem_outsideImage [Finite V] (A B I : Finset V) (hAB : Disjoint A B)
    {b : V} (hb : b ∈ B) : contract A B b ∉ outsideImage A B I := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  intro h
  simp only [outsideImage, Finset.mem_image] at h
  rcases h with ⟨v, hv, hvb⟩
  have hv' := (mem_outsidePart_iff A B I v).mp hv
  have hbA : b ∉ A := fun hba ↦ Finset.disjoint_left.mp hAB hba hb
  have hval := congrArg Subtype.val hvb
  simp [contract, preContract, hbA, hb, hv'.2.1, hv'.2.2] at hval

omit [Fintype V] in
theorem insert_left_outsideImage_card [Finite V] (A B I : Finset V) {a : V} (ha : a ∈ A) :
    (insert (contract A B a) (outsideImage A B I)).card =
      (outsidePart A B I).card + 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rw [Finset.card_insert_of_not_mem (contract_left_not_mem_outsideImage A B I ha)]
  rw [outsideImage_card]

omit [Fintype V] in
theorem insert_right_outsideImage_card [Finite V] (A B I : Finset V) (hAB : Disjoint A B)
    {b : V} (hb : b ∈ B) :
    (insert (contract A B b) (outsideImage A B I)).card =
      (outsidePart A B I).card + 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rw [Finset.card_insert_of_not_mem (contract_right_not_mem_outsideImage A B I hAB hb)]
  rw [outsideImage_card]

omit [Fintype V] in
theorem insert_both_outsideImage_card [Finite V] (A B I : Finset V) (hAB : Disjoint A B)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B) :
    (insert (contract A B a) (insert (contract A B b) (outsideImage A B I))).card =
      (outsidePart A B I).card + 2 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hright := contract_right_not_mem_outsideImage A B I hAB hb
  have hleft : contract A B a ∉ insert (contract A B b) (outsideImage A B I) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨contract_ne_left_right A B hAB ha hb, contract_left_not_mem_outsideImage A B I ha⟩
  rw [Finset.card_insert_of_not_mem hleft, Finset.card_insert_of_not_mem hright]
  rw [outsideImage_card]

/-- Portion of an independent set lying on the old even cycle. -/
def cyclePart (A B I : Finset V) : Finset V := I ∩ (A ∪ B)

omit [Fintype V] in
theorem outsidePart_eq_sdiff [Finite V] (A B I : Finset V) :
    outsidePart A B I = I \ (A ∪ B) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  ext v
  simp [outsidePart]

omit [Fintype V] in
theorem outside_cycle_card_decomposition [Finite V] (A B I : Finset V) :
    (outsidePart A B I).card + (cyclePart A B I).card = I.card := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rw [outsidePart_eq_sdiff]
  exact Finset.card_sdiff_add_card_inter I (A ∪ B)

/-- Old vertices outside the contracted fibers whose images lie in `S`. -/
def outsidePreimage (A B : Finset V) (S : Finset (ContractVertex A B)) : Finset V :=
  Finset.univ.filter fun v ↦ contract A B v ∈ S ∧ v ∉ A ∧ v ∉ B

theorem mem_outsidePreimage_iff (A B : Finset V) (S : Finset (ContractVertex A B))
    (v : V) :
    v ∈ outsidePreimage A B S ↔ contract A B v ∈ S ∧ v ∉ A ∧ v ∉ B := by
  simp [outsidePreimage]

theorem outsideImage_outsidePreimage_subset (A B : Finset V)
    (S : Finset (ContractVertex A B)) :
    outsideImage A B (outsidePreimage A B S) ⊆ S := by
  intro x hx
  simp only [outsideImage, Finset.mem_image] at hx
  rcases hx with ⟨v, hv, rfl⟩
  exact ((mem_outsidePreimage_iff A B S v).mp
    ((mem_outsidePart_iff A B (outsidePreimage A B S) v).mp hv).1).1

theorem outsidePart_outsidePreimage (A B : Finset V)
    (S : Finset (ContractVertex A B)) :
    outsidePart A B (outsidePreimage A B S) = outsidePreimage A B S := by
  apply Finset.filter_eq_self.mpr
  intro v hv
  exact ((mem_outsidePreimage_iff A B S v).mp hv).2

theorem outsideImage_outsidePreimage_card (A B : Finset V)
    (S : Finset (ContractVertex A B)) :
    (outsideImage A B (outsidePreimage A B S)).card =
      (outsidePreimage A B S).card := by
  rw [outsideImage_card, outsidePart_outsidePreimage]

theorem mem_eq_left_or_eq_right_or_mem_outsideImage (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B)) {x : ContractVertex A B} (hx : x ∈ S) :
    x = contract A B a ∨ x = contract A B b ∨
      x ∈ outsideImage A B (outsidePreimage A B S) := by
  obtain ⟨v, hv⟩ := x.property
  have hcv : contract A B v = x := by
    apply Subtype.ext
    exact hv
  by_cases hvA : v ∈ A
  · left
    exact hcv.symm.trans (contract_eq_of_mem_left A B hvA ha)
  · by_cases hvB : v ∈ B
    · right; left
      exact hcv.symm.trans (contract_eq_of_mem_right A B hAB hvB hb)
    · right; right
      simp only [outsideImage, Finset.mem_image]
      refine ⟨v, ?_, hcv⟩
      apply (mem_outsidePart_iff A B (outsidePreimage A B S) v).mpr
      exact ⟨(mem_outsidePreimage_iff A B S v).mpr ⟨hcv.symm ▸ hx, hvA, hvB⟩, hvA, hvB⟩

theorem contracted_set_eq_outside_of_neither (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∉ S) (hbS : contract A B b ∉ S) :
    S = outsideImage A B (outsidePreimage A B S) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases mem_eq_left_or_eq_right_or_mem_outsideImage A B hAB ha hb S hx with
      rfl | rfl | hx
    · exact (haS hx).elim
    · exact (hbS hx).elim
    · exact hx
  · exact outsideImage_outsidePreimage_subset A B S

theorem contracted_set_eq_insert_left (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∈ S) (hbS : contract A B b ∉ S) :
    S = insert (contract A B a) (outsideImage A B (outsidePreimage A B S)) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases mem_eq_left_or_eq_right_or_mem_outsideImage A B hAB ha hb S hx with
      rfl | rfl | hx
    · simp
    · exact (hbS hx).elim
    · simp [hx]
  · intro x hx
    simp only [Finset.mem_insert] at hx
    exact hx.elim (fun h ↦ h ▸ haS)
      (fun h ↦ outsideImage_outsidePreimage_subset A B S h)

theorem contracted_set_eq_insert_right (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∉ S) (hbS : contract A B b ∈ S) :
    S = insert (contract A B b) (outsideImage A B (outsidePreimage A B S)) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases mem_eq_left_or_eq_right_or_mem_outsideImage A B hAB ha hb S hx with
      rfl | rfl | hx
    · exact (haS hx).elim
    · simp
    · simp [hx]
  · intro x hx
    simp only [Finset.mem_insert] at hx
    exact hx.elim (fun h ↦ h ▸ hbS)
      (fun h ↦ outsideImage_outsidePreimage_subset A B S h)

theorem contracted_set_eq_insert_both (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∈ S) (hbS : contract A B b ∈ S) :
    S = insert (contract A B a)
      (insert (contract A B b) (outsideImage A B (outsidePreimage A B S))) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases mem_eq_left_or_eq_right_or_mem_outsideImage A B hAB ha hb S hx with
      rfl | rfl | hx <;> simp_all
  · intro x hx
    simp only [Finset.mem_insert] at hx
    rcases hx with h | h | h
    · exact h ▸ haS
    · exact h ▸ hbS
    · exact outsideImage_outsidePreimage_subset A B S h

theorem outsidePreimage_card_eq_of_neither (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∉ S) (hbS : contract A B b ∉ S) :
    (outsidePreimage A B S).card = S.card := by
  have hset := contracted_set_eq_outside_of_neither A B hAB ha hb S haS hbS
  have hcard := congrArg Finset.card hset
  have hout := outsideImage_outsidePreimage_card A B S
  omega

theorem outsidePreimage_card_add_one_of_left (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∈ S) (hbS : contract A B b ∉ S) :
    (outsidePreimage A B S).card + 1 = S.card := by
  have hset := contracted_set_eq_insert_left A B hAB ha hb S haS hbS
  have hcard := congrArg Finset.card hset
  have hins := insert_left_outsideImage_card A B (outsidePreimage A B S) ha
  rw [outsidePart_outsidePreimage] at hins
  omega

theorem outsidePreimage_card_add_one_of_right (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∉ S) (hbS : contract A B b ∈ S) :
    (outsidePreimage A B S).card + 1 = S.card := by
  have hset := contracted_set_eq_insert_right A B hAB ha hb S haS hbS
  have hcard := congrArg Finset.card hset
  have hins := insert_right_outsideImage_card A B (outsidePreimage A B S) hAB hb
  rw [outsidePart_outsidePreimage] at hins
  omega

theorem outsidePreimage_card_add_two_of_both (A B : Finset V)
    (hAB : Disjoint A B) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (S : Finset (ContractVertex A B))
    (haS : contract A B a ∈ S) (hbS : contract A B b ∈ S) :
    (outsidePreimage A B S).card + 2 = S.card := by
  have hset := contracted_set_eq_insert_both A B hAB ha hb S haS hbS
  have hcard := congrArg Finset.card hset
  have hins := insert_both_outsideImage_card A B (outsidePreimage A B S) hAB ha hb
  rw [outsidePart_outsidePreimage] at hins
  omega

end Cardinalities

section WitnessLift

omit [Fintype V] in
/-- The common 0/1/2-contracted-vertex witness lift.  The cycle classification
is supplied separately: an independent intersection of size `p` must be one
of the two alternating sides.  When it is smaller, dropping the cycle part
costs at most `p-1`; when it is a full side, its entire fiber can safely be
replaced by the corresponding contracted vertex. -/
theorem exists_contracted_independent_witness [Finite V]
    (G : SimpleGraph V) (A B I : Finset V) (p : ℕ) (hAB : Disjoint A B)
    {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (hp : 1 ≤ p) (hAcard : A.card = p) (hBcard : B.card = p)
    (S : Finset (ContractVertex A B))
    (hI : G.IsIndepSet I)
    (houtside : ∀ v ∈ I, v ∉ A → v ∉ B → contract A B v ∈ S)
    (hcycle : (cyclePart A B I).card ≤ p)
    (hfull : (cyclePart A B I).card = p →
      cyclePart A B I = A ∨ cyclePart A B I = B)
    (hleft : cyclePart A B I = A → contract A B a ∈ S)
    (hright : cyclePart A B I = B → contract A B b ∈ S) :
    ∃ J : Finset (ContractVertex A B), J ⊆ S ∧
      (contractGraph G A B).IsIndepSet J ∧ I.card ≤ J.card + (p - 1) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have houtside_subset : outsideImage A B I ⊆ S := by
    intro x hx
    simp only [outsideImage, Finset.mem_image] at hx
    rcases hx with ⟨v, hv, rfl⟩
    have hv' := (mem_outsidePart_iff A B I v).mp hv
    exact houtside v hv'.1 hv'.2.1 hv'.2.2
  by_cases hsmall : (cyclePart A B I).card < p
  · refine ⟨outsideImage A B I, houtside_subset,
      isIndepSet_outsideImage G A B I hI, ?_⟩
    have hdecomp := outside_cycle_card_decomposition A B I
    have himage := outsideImage_card A B I
    omega
  · have heq : (cyclePart A B I).card = p := by omega
    rcases hfull heq with hKA | hKB
    · let J := insert (contract A B a) (outsideImage A B I)
      have hAI : A ⊆ I := by
        intro v hv
        have hvK : v ∈ cyclePart A B I := by simpa [hKA] using hv
        exact (Finset.mem_inter.mp hvK).1
      refine ⟨J, ?_, isIndepSet_insert_left G A B I ha hAI hI, ?_⟩
      · intro x hx
        simp only [J, Finset.mem_insert] at hx
        exact hx.elim (fun h ↦ h ▸ hleft hKA) (fun h ↦ houtside_subset h)
      · have hdecomp := outside_cycle_card_decomposition A B I
        have hJcard := insert_left_outsideImage_card A B I ha
        dsimp only [J]
        rw [hKA, hAcard] at hdecomp
        omega
    · let J := insert (contract A B b) (outsideImage A B I)
      have hBI : B ⊆ I := by
        intro v hv
        have hvK : v ∈ cyclePart A B I := by simpa [hKB] using hv
        exact (Finset.mem_inter.mp hvK).1
      refine ⟨J, ?_, isIndepSet_insert_right G A B I hAB hb hBI hI, ?_⟩
      · intro x hx
        simp only [J, Finset.mem_insert] at hx
        exact hx.elim (fun h ↦ h ▸ hright hKB) (fun h ↦ houtside_subset h)
      · have hdecomp := outside_cycle_card_decomposition A B I
        have hJcard := insert_right_outsideImage_card A B I hAB hb
        dsimp only [J]
        rw [hKB, hBcard] at hdecomp
        omega

end WitnessLift

end Erdos922EvenHole
