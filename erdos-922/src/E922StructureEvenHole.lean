/-
Inherited Folkman/Erdos922 finite-proof segment, original lines1616--1982.
Source: plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos922.lean; SHA256
0bc22004ecbe76ab3cc3f263c29c76994b39017828ea835d987139fa324b9971.
Original mathematics: Jon Folkman. Original formal authors: Codex; GPT-5.6 Sol.
Local Lean4.19 port under Gott-L's direction, with Codex/B implementation.
Private compatibility experiment; upstream fixed license remains unverified.
No new mathematical discovery or completed Folkman supplier is claimed.
-/
import E922StructureContraction

open SimpleGraph
open scoped ENat


open SimpleGraph

namespace Erdos922
namespace EvenHole

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

abbrev CV (A B : Finset V) := Erdos922EvenHole.ContractVertex A B
abbrev qmap (A B : Finset V) := Erdos922EvenHole.contract A B
abbrev qgraph (G : SimpleGraph V) (A B : Finset V) :=
  Erdos922EvenHole.contractGraph G A B

open Erdos922EvenHole

/-- The contraction map is a graph homomorphism when its two nontrivial
fibers are independent. -/
def contractionHom (G : SimpleGraph V) (A B : Finset V) (hAB : Disjoint A B)
    (hA : G.IsIndepSet A) (hB : G.IsIndepSet B) : G →g qgraph G A B where
  toFun := qmap A B
  map_rel' := by
    intro u v huv
    apply SimpleGraph.mapFunctionCompat_adj_apply huv
    intro heq
    by_cases huA : u ∈ A
    · have hpv : preContract A B v = Sum.inr false := by
        have hval := congrArg Subtype.val heq
        simpa [qmap, contract, preContract, huA] using hval.symm
      have hvA := (preContract_eq_inr_false_iff A B v).mp hpv
      exact hA huA hvA huv.ne huv
    · by_cases huB : u ∈ B
      · have hpv : preContract A B v = Sum.inr true := by
          have hval := congrArg Subtype.val heq
          simpa [qmap, contract, preContract, huA, huB] using hval.symm
        have hvB := (preContract_eq_inr_true_iff A B hAB v).mp hpv
        exact hB huB hvB huv.ne huv
      · have hpv : preContract A B v = Sum.inl u := by
          have hval := congrArg Subtype.val heq
          simpa [qmap, contract, preContract, huA, huB] using hval.symm
        have hvu := (preContract_eq_inl_iff A B v u).mp hpv |>.1
        exact huv.ne hvu.symm

omit [Fintype V] in
theorem chromaticNumber_le_contraction [Finite V] (G : SimpleGraph V) (A B : Finset V)
    (hAB : Disjoint A B) (hA : G.IsIndepSet A) (hB : G.IsIndepSet B) :
    G.chromaticNumber ≤ (qgraph G A B).chromaticNumber := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  apply SimpleGraph.chromaticNumber_le_of_forall_imp
  intro n hn
  exact ⟨hn.some.comp (contractionHom G A B hAB hA hB)⟩

/-- The exact abstract information about an induced even cycle used by the
contraction argument. -/
structure Configuration (G : SimpleGraph V) (A B : Finset V) (p : ℕ) : Prop where
  disjoint : Disjoint A B
  two_le : 2 ≤ p
  card_left : A.card = p
  card_right : B.card = p
  indep_left : G.IsIndepSet A
  indep_right : G.IsIndepSet B
  cycle_bound : ∀ I : Finset V, I ⊆ A ∪ B → G.IsIndepSet I → I.card ≤ p
  cycle_eq_of_card : ∀ I : Finset V, I ⊆ A ∪ B → G.IsIndepSet I →
    I.card = p → I = A ∨ I = B

omit [Fintype V] in
theorem potential_le_of_witness_lift [Finite V]
    (G : SimpleGraph V) (A B : Finset V) (p : ℕ)
    (S : Finset (CV A B)) (H : Finset V) (hp : 1 ≤ p)
    (hcard : (H.card : ℤ) = (S.card : ℤ) + 2 * (p : ℤ) - 2)
    (hlift : ∀ I : Finset V, I ⊆ H → G.IsIndepSet I →
      ∃ J : Finset (CV A B), J ⊆ S ∧ (qgraph G A B).IsIndepSet J ∧
        I.card ≤ J.card + (p - 1)) :
    Erdos922.potential (qgraph G A B) S ≤ Erdos922.potential G H := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨I, hIH, hIind, hIcard⟩ := Erdos922.exists_maximum_independent_subset G H
  obtain ⟨J, hJS, hJind, hIJ⟩ := hlift I hIH hIind
  have hJalpha : J.card ≤ Erdos922.alphaOn (qgraph G A B) S :=
    Erdos922.card_le_alphaOn hJS hJind
  rw [Erdos922.potential, Erdos922.potential, ← hIcard]
  omega

omit [Fintype V] in
/-- Every independent set in a proposed lifted vertex set gives the cycle
classification required by the witness lift. -/
theorem cyclePart_data [Finite V] (G : SimpleGraph V) (A B I : Finset V) (p : ℕ)
    (hC : Configuration G A B p) (hI : G.IsIndepSet I) :
    (cyclePart A B I).card ≤ p ∧
      ((cyclePart A B I).card = p → cyclePart A B I = A ∨ cyclePart A B I = B) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  have hsub : cyclePart A B I ⊆ A ∪ B := by simp [cyclePart]
  have hind : G.IsIndepSet (cyclePart A B I) := hI.mono (by simp [cyclePart])
  exact ⟨hC.cycle_bound _ hsub hind, hC.cycle_eq_of_card _ hsub hind⟩

/-- The old outside vertices are disjoint from the old cycle. -/
theorem outsidePreimage_disjoint_cycle (A B : Finset V) (S : Finset (CV A B)) :
    Disjoint (outsidePreimage A B S) (A ∪ B) := by
  rw [Finset.disjoint_left]
  intro v hvT hvC
  have hvout := (mem_outsidePreimage_iff A B S v).mp hvT
  rcases Finset.mem_union.mp hvC with hvA | hvB
  · exact hvout.2.1 hvA
  · exact hvout.2.2 hvB

omit [Fintype V] in
/-- All cycle cardinalities needed in the three lift cases. -/
theorem cycle_card [Finite V] (G : SimpleGraph V) (A B : Finset V) (p : ℕ)
    (hC : Configuration G A B p) : (A ∪ B).card = 2 * p := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rw [Finset.card_union_of_disjoint hC.disjoint, hC.card_left, hC.card_right]
  omega

/-- Contracting an abstract even-hole configuration cannot increase Folkman's
maximum signed deficiency. -/
theorem f_contraction_le (G : SimpleGraph V) (A B : Finset V) (p : ℕ)
    (hC : Configuration G A B p) :
    Erdos922.f (qgraph G A B) ≤ Erdos922.f G := by
  have hp : 1 ≤ p := (by omega : 1 ≤ 2).trans hC.two_le
  have hAne : A.Nonempty := Finset.card_pos.mp (by rw [hC.card_left]; exact Nat.zero_lt_of_lt hp)
  have hBne : B.Nonempty := Finset.card_pos.mp (by rw [hC.card_right]; exact Nat.zero_lt_of_lt hp)
  obtain ⟨a, ha⟩ := hAne
  obtain ⟨b, hb⟩ := hBne
  rw [Erdos922.f_le_iff_forall_potential_le]
  intro S
  let T := outsidePreimage A B S
  let C := A ∪ B
  have hTC : Disjoint T C := outsidePreimage_disjoint_cycle A B S
  have hCcard : C.card = 2 * p := cycle_card G A B p hC
  by_cases haS : contract A B a ∈ S
  · by_cases hbS : contract A B b ∈ S
    · -- Both contracted vertices occur: lift all of the old cycle.
      let H := T ∪ C
      have hTcard := outsidePreimage_card_add_two_of_both
        A B hC.disjoint ha hb S haS hbS
      have hHcardNat : H.card = T.card + C.card := by
        exact Finset.card_union_of_disjoint hTC
      have hHcard : (H.card : ℤ) = (S.card : ℤ) + 2 * (p : ℤ) - 2 := by
        have hTcardZ : (T.card : ℤ) + 2 = (S.card : ℤ) := by exact_mod_cast hTcard
        have hCcardZ : (C.card : ℤ) = 2 * (p : ℤ) := by exact_mod_cast hCcard
        have hHcardZ : (H.card : ℤ) = (T.card : ℤ) + C.card := by
          exact_mod_cast hHcardNat
        omega
      have hlift : ∀ I : Finset V, I ⊆ H → G.IsIndepSet I →
          ∃ J : Finset (CV A B), J ⊆ S ∧ (qgraph G A B).IsIndepSet J ∧
            I.card ≤ J.card + (p - 1) := by
        intro I hIH hI
        have hout : ∀ v ∈ I, v ∉ A → v ∉ B → contract A B v ∈ S := by
          intro v hvI hvA hvB
          have hvH := hIH hvI
          simp only [H, Finset.mem_union] at hvH
          rcases hvH with hvT | hvC
          · exact (mem_outsidePreimage_iff A B S v).mp hvT |>.1
          · rcases Finset.mem_union.mp hvC with hv | hv
            · exact (hvA hv).elim
            · exact (hvB hv).elim
        have hd := cyclePart_data G A B I p hC hI
        exact exists_contracted_independent_witness G A B I p hC.disjoint ha hb
          hp hC.card_left hC.card_right S hI hout hd.1 hd.2
          (fun _ ↦ haS) (fun _ ↦ hbS)
      exact (potential_le_of_witness_lift G A B p S H hp hHcard hlift).trans
        (Erdos922.potential_le_f G H)
    · -- Only the left contracted vertex occurs: delete one right vertex.
      let D := C.erase b
      let H := T ∪ D
      have hbC : b ∈ C := Finset.mem_union_right A hb
      have hDcard : D.card = 2 * p - 1 := by
        dsimp only [D]
        rw [Finset.card_erase_of_mem hbC, hCcard]
      have hTD : Disjoint T D := hTC.mono_right (Finset.erase_subset _ _)
      have hTcard := outsidePreimage_card_add_one_of_left
        A B hC.disjoint ha hb S haS hbS
      have hHcardNat : H.card = T.card + D.card := Finset.card_union_of_disjoint hTD
      have hHcard : (H.card : ℤ) = (S.card : ℤ) + 2 * (p : ℤ) - 2 := by
        have hTcardZ : (T.card : ℤ) + 1 = (S.card : ℤ) := by exact_mod_cast hTcard
        have hDcardZ : (D.card : ℤ) = 2 * (p : ℤ) - 1 := by
          rw [hDcard, Nat.cast_sub (by omega : 1 ≤ 2 * p)]
          norm_num
        have hHcardZ : (H.card : ℤ) = (T.card : ℤ) + D.card := by
          exact_mod_cast hHcardNat
        omega
      have hbA : b ∉ A := fun hba ↦ Finset.disjoint_left.mp hC.disjoint hba hb
      have hlift : ∀ I : Finset V, I ⊆ H → G.IsIndepSet I →
          ∃ J : Finset (CV A B), J ⊆ S ∧ (qgraph G A B).IsIndepSet J ∧
            I.card ≤ J.card + (p - 1) := by
        intro I hIH hI
        have hout : ∀ v ∈ I, v ∉ A → v ∉ B → contract A B v ∈ S := by
          intro v hvI hvA hvB
          have hvH := hIH hvI
          simp only [H, Finset.mem_union] at hvH
          rcases hvH with hvT | hvD
          · exact (mem_outsidePreimage_iff A B S v).mp hvT |>.1
          · have hvC : v ∈ C := (Finset.mem_erase.mp hvD).2
            rcases Finset.mem_union.mp hvC with hv | hv
            · exact (hvA hv).elim
            · exact (hvB hv).elim
        have hd := cyclePart_data G A B I p hC hI
        apply exists_contracted_independent_witness G A B I p hC.disjoint ha hb
          hp hC.card_left hC.card_right S hI hout hd.1 hd.2
          (fun _ ↦ haS)
        intro hKB
        exfalso
        have hbK : b ∈ cyclePart A B I := by simpa [hKB] using hb
        have hbI : b ∈ I := (Finset.mem_inter.mp hbK).1
        have hbH := hIH hbI
        rcases Finset.mem_union.mp hbH with hbT | hbD
        · exact ((mem_outsidePreimage_iff A B S b).mp hbT).2.2 hb
        · exact (Finset.mem_erase.mp hbD).1 rfl
      exact (potential_le_of_witness_lift G A B p S H hp hHcard hlift).trans
        (Erdos922.potential_le_f G H)
  · by_cases hbS : contract A B b ∈ S
    · -- Only the right contracted vertex occurs: delete one left vertex.
      let D := C.erase a
      let H := T ∪ D
      have haC : a ∈ C := Finset.mem_union_left B ha
      have hDcard : D.card = 2 * p - 1 := by
        dsimp only [D]
        rw [Finset.card_erase_of_mem haC, hCcard]
      have hTD : Disjoint T D := hTC.mono_right (Finset.erase_subset _ _)
      have hTcard := outsidePreimage_card_add_one_of_right
        A B hC.disjoint ha hb S haS hbS
      have hHcardNat : H.card = T.card + D.card := Finset.card_union_of_disjoint hTD
      have hHcard : (H.card : ℤ) = (S.card : ℤ) + 2 * (p : ℤ) - 2 := by
        have hTcardZ : (T.card : ℤ) + 1 = (S.card : ℤ) := by exact_mod_cast hTcard
        have hDcardZ : (D.card : ℤ) = 2 * (p : ℤ) - 1 := by
          rw [hDcard, Nat.cast_sub (by omega : 1 ≤ 2 * p)]
          norm_num
        have hHcardZ : (H.card : ℤ) = (T.card : ℤ) + D.card := by
          exact_mod_cast hHcardNat
        omega
      have hlift : ∀ I : Finset V, I ⊆ H → G.IsIndepSet I →
          ∃ J : Finset (CV A B), J ⊆ S ∧ (qgraph G A B).IsIndepSet J ∧
            I.card ≤ J.card + (p - 1) := by
        intro I hIH hI
        have hout : ∀ v ∈ I, v ∉ A → v ∉ B → contract A B v ∈ S := by
          intro v hvI hvA hvB
          have hvH := hIH hvI
          simp only [H, Finset.mem_union] at hvH
          rcases hvH with hvT | hvD
          · exact (mem_outsidePreimage_iff A B S v).mp hvT |>.1
          · have hvC : v ∈ C := (Finset.mem_erase.mp hvD).2
            rcases Finset.mem_union.mp hvC with hv | hv
            · exact (hvA hv).elim
            · exact (hvB hv).elim
        have hd := cyclePart_data G A B I p hC hI
        apply exists_contracted_independent_witness G A B I p hC.disjoint ha hb
          hp hC.card_left hC.card_right S hI hout hd.1 hd.2
        · intro hKA
          exfalso
          have haK : a ∈ cyclePart A B I := by simpa [hKA] using ha
          have haI : a ∈ I := (Finset.mem_inter.mp haK).1
          have haH := hIH haI
          rcases Finset.mem_union.mp haH with haT | haD
          · exact ((mem_outsidePreimage_iff A B S a).mp haT).2.1 ha
          · exact (Finset.mem_erase.mp haD).1 rfl
        · exact fun _ ↦ hbS
      exact (potential_le_of_witness_lift G A B p S H hp hHcard hlift).trans
        (Erdos922.potential_le_f G H)
    · -- Neither contracted vertex occurs: no cycle vertices are lifted.
      let H := T
      have hTcard := outsidePreimage_card_eq_of_neither
        A B hC.disjoint ha hb S haS hbS
      have hHcard : (H.card : ℤ) = (S.card : ℤ) + 2 * (1 : ℤ) - 2 := by
        dsimp only [H]
        have hTcardZ : (T.card : ℤ) = (S.card : ℤ) := by exact_mod_cast hTcard
        omega
      have hlift : ∀ I : Finset V, I ⊆ H → G.IsIndepSet I →
          ∃ J : Finset (CV A B), J ⊆ S ∧ (qgraph G A B).IsIndepSet J ∧
            I.card ≤ J.card + (1 - 1) := by
        intro I hIH hI
        have houtpart : outsidePart A B I = I := by
          apply Finset.filter_eq_self.mpr
          intro v hvI
          have hvT : v ∈ T := hIH hvI
          exact ((mem_outsidePreimage_iff A B S v).mp hvT).2
        refine ⟨outsideImage A B I, ?_, isIndepSet_outsideImage G A B I hI, ?_⟩
        · intro x hx
          simp only [outsideImage, Finset.mem_image] at hx
          rcases hx with ⟨v, hv, rfl⟩
          have hvI := (mem_outsidePart_iff A B I v).mp hv |>.1
          exact (mem_outsidePreimage_iff A B S v).mp (hIH hvI) |>.1
        · have hj := outsideImage_card A B I
          rw [houtpart] at hj
          omega
      exact (potential_le_of_witness_lift G A B 1 S H (by omega) hHcard hlift).trans
        (Erdos922.potential_le_f G H)

/-- A genuine contraction is strictly smaller: the left fiber alone contains
at least two vertices. -/
theorem card_contractVertex_lt (G : SimpleGraph V) (A B : Finset V) (p : ℕ)
    (hC : Configuration G A B p) :
    Fintype.card (CV A B) < Fintype.card V := by
  have hle : Fintype.card (CV A B) ≤ Fintype.card V :=
    Fintype.card_range_le (preContract A B)
  apply lt_of_le_of_ne hle
  intro heq
  have hcardEq : Fintype.card V = Fintype.card (CV A B) := heq.symm
  let e : V ≃ CV A B := Fintype.equivOfCardEq hcardEq
  have hsurj : Function.Surjective (contract A B) := by
    intro x
    obtain ⟨v, hv⟩ := x.property
    refine ⟨v, ?_⟩
    apply Subtype.ext
    exact hv
  have hinj : Function.Injective (contract A B) :=
    (Finite.injective_iff_surjective_of_equiv e).mpr hsurj
  have hp0 : 0 < p := lt_of_lt_of_le (by omega : 0 < 2) hC.two_le
  have hAne : A.Nonempty := Finset.card_pos.mp (hC.card_left.symm ▸ hp0)
  obtain ⟨a, ha⟩ := hAne
  have hsub : A ⊆ {a} := by
    intro v hv
    simp only [Finset.mem_singleton]
    apply hinj
    exact contract_eq_of_mem_left A B hv ha
  have hcardle := Finset.card_le_card hsub
  rw [hC.card_left] at hcardle
  simpa using hC.two_le.trans hcardle

/-- The promised structural consequence of minimal-counterexample induction:
a minimal counterexample to Folkman's bound has no abstract even-hole
configuration. -/
theorem no_configuration_of_minimal_counterexample
    (G : SimpleGraph V)
    (hminimal : ∀ {W : Type u} [Fintype W] [DecidableEq W]
      (H : SimpleGraph W), Fintype.card W < Fintype.card V →
        H.chromaticNumber ≤ ((Erdos922.f H).toNat + 2 : ℕ∞))
    (hcounter : ¬ G.chromaticNumber ≤ ((Erdos922.f G).toNat + 2 : ℕ∞)) :
    ¬ ∃ (A B : Finset V) (p : ℕ), Configuration G A B p := by
  rintro ⟨A, B, p, hC⟩
  have hsmall := card_contractVertex_lt G A B p hC
  have hmin := hminimal (qgraph G A B) hsmall
  have hchrom := chromaticNumber_le_contraction G A B hC.disjoint hC.indep_left hC.indep_right
  have hf := f_contraction_le G A B p hC
  have hnat : (Erdos922.f (qgraph G A B)).toNat ≤ (Erdos922.f G).toNat :=
    Int.toNat_le_toNat hf
  have henat : (((Erdos922.f (qgraph G A B)).toNat + 2 : ℕ) : ℕ∞) ≤
      ((Erdos922.f G).toNat + 2 : ℕ∞) := by
    exact_mod_cast Nat.add_le_add_right hnat 2
  exact hcounter (hchrom.trans (hmin.trans henat))

omit [DecidableEq V] in
/-- The global maximum used by the endpoint/core file is the localized
maximum on the full vertex finset used by the minimal-counterexample file. -/
theorem f_eq_fOn_univ (G : SimpleGraph V) :
    Erdos922.f G = Erdos922FullB.fOn G Finset.univ := by
  classical
  rfl

/-- The final form consumed by the repository's strong-induction framework. -/
theorem no_configuration_of_orderMinimalCounterexample
    (G : SimpleGraph V) (hmin : Erdos922FullB.IsOrderMinimalCounterexample G) :
    ¬ ∃ (A B : Finset V) (p : ℕ), Configuration G A B p := by
  apply no_configuration_of_minimal_counterexample G
  · intro W _ _ H hcard
    have hsmall := hmin.smaller H hcard
    have hchrom := hsmall.chromaticNumber_le
    simpa only [Erdos922FullB.FolkmanBound, ← f_eq_fOn_univ,
      Nat.cast_add, Nat.cast_ofNat] using hchrom
  · intro hbound
    apply hmin.counterexample
    rw [Erdos922FullB.FolkmanBound, ← SimpleGraph.chromaticNumber_le_iff_colorable]
    simpa only [← f_eq_fOn_univ, Nat.cast_add, Nat.cast_ofNat] using hbound

end EvenHole
end Erdos922
