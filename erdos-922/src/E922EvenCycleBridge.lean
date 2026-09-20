/-
Inherited EvenCycleBridge, original Erdos922.lean lines3772--4200.
plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos922.lean, SHA256
0bc22004ecbe76ab3cc3f263c29c76994b39017828ea835d987139fa324b9971.
Informal author: Jon Folkman. Formal authors: Codex; GPT-5.6 Sol.
Local Lean4.19 port under Gott-L's direction by Codex/B.
Private local work; upstream license unverified; no novelty claim.
-/
import E922DiamondMinimal

open SimpleGraph
open scoped ENat

namespace Erdos922Recolor

universe u

variable {V : Type u}

namespace EvenCycleBridge

/-- Identify a cyclic index with a pair number and a parity bit. -/
def pairEquiv (p : ℕ) : Fin p × Fin 2 ≃ Fin (2 * p) :=
  finProdFinEquiv.trans (finCongr (Nat.mul_comm p 2))

def leftEmbedding (p : ℕ) : Fin p ↪ Fin (2 * p) where
  toFun i := pairEquiv p (i, 0)
  inj' _ _ h := congrArg Prod.fst ((pairEquiv p).injective h)

def rightEmbedding (p : ℕ) : Fin p ↪ Fin (2 * p) where
  toFun i := pairEquiv p (i, 1)
  inj' _ _ h := congrArg Prod.fst ((pairEquiv p).injective h)

def leftIndices (p : ℕ) : Finset (Fin (2 * p)) :=
  Finset.univ.map (leftEmbedding p)

def rightIndices (p : ℕ) : Finset (Fin (2 * p)) :=
  Finset.univ.map (rightEmbedding p)

def nextIndex (p : ℕ) (hp : 1 ≤ p) (i : Fin p) : Fin p :=
  ⟨(i.val + 1) % p, Nat.mod_lt _ (by omega)⟩

@[simp] theorem pairEquiv_val (p : ℕ) (i : Fin p) (b : Fin 2) :
    (pairEquiv p (i, b)).val = b.val + 2 * i.val := rfl

/-- The two vertices in one consecutive pair are adjacent on the cycle. -/
theorem pair_adj (p : ℕ) (_hp : 1 ≤ p) (i : Fin p) :
    (SimpleGraph.cycleGraph (2 * p)).Adj
      (pairEquiv p (i, 0)) (pairEquiv p (i, 1)) := by
  rw [SimpleGraph.cycleGraph_adj']
  right
  rw [Fin.coe_sub_iff_le.mpr (by
    rw [Fin.le_iff_val_le_val, pairEquiv_val, pairEquiv_val]
    omega)]
  rw [pairEquiv_val, pairEquiv_val]
  omega

/-- The odd vertex of a pair is adjacent to the even vertex of the next
cyclic pair. -/
theorem pair_next_adj (p : ℕ) (hp : 1 ≤ p) (i : Fin p) :
    (SimpleGraph.cycleGraph (2 * p)).Adj
      (pairEquiv p (i, 1)) (pairEquiv p (nextIndex p hp i, 0)) := by
  rw [SimpleGraph.cycleGraph_adj']
  by_cases hi : i.val + 1 < p
  · right
    have hval : (nextIndex p hp i).val = i.val + 1 := by
      simp [nextIndex, Nat.mod_eq_of_lt hi]
    rw [Fin.coe_sub_iff_le.mpr]
    · rw [pairEquiv_val, pairEquiv_val, hval]
      omega
    · rw [Fin.le_iff_val_le_val, pairEquiv_val, pairEquiv_val, hval]
      omega
  · right
    have hilast : i.val = p - 1 := by omega
    have hnext : (nextIndex p hp i).val = 0 := by
      simp only [nextIndex]
      have hip : i.val + 1 = p := by omega
      simp [hip]
    rw [Fin.coe_sub_iff_lt.mpr]
    · rw [pairEquiv_val, pairEquiv_val, hilast, hnext]
      omega
    · rw [Fin.lt_def, pairEquiv_val, pairEquiv_val, hilast, hnext]
      omega

theorem independent_card_le (p : ℕ) (hp : 1 ≤ p)
    (J : Finset (Fin (2 * p)))
    (hJ : (SimpleGraph.cycleGraph (2 * p)).IsIndepSet J) :
    J.card ≤ p := by
  classical
  let f : {x // x ∈ J} → Fin p := fun x ↦ ((pairEquiv p).symm x.1).1
  have hf : Function.Injective f := by
    intro x y hxyfst
    apply Subtype.ext
    by_contra hxy
    let cx := (pairEquiv p).symm x.1
    let cy := (pairEquiv p).symm y.1
    have hfst : cx.1 = cy.1 := hxyfst
    have hsnd : cx.2 ≠ cy.2 := by
      intro hsnd
      have hc : cx = cy := Prod.ext hfst hsnd
      apply hxy
      calc
        x.1 = pairEquiv p cx := ((pairEquiv p).apply_symm_apply x.1).symm
        _ = pairEquiv p cy := congrArg (pairEquiv p) hc
        _ = y.1 := (pairEquiv p).apply_symm_apply y.1
    have hbits : (cx.2 = 0 ∧ cy.2 = 1) ∨ (cx.2 = 1 ∧ cy.2 = 0) := by
      have hcxv : cx.2.val = 0 ∨ cx.2.val = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega)
      have hcyv : cy.2.val = 0 ∨ cy.2.val = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega)
      rcases hcxv with hcxv | hcxv <;> rcases hcyv with hcyv | hcyv
      · exact (hsnd (Fin.ext (hcxv.trans hcyv.symm))).elim
      · exact Or.inl ⟨Fin.ext hcxv, Fin.ext hcyv⟩
      · exact Or.inr ⟨Fin.ext hcxv, Fin.ext hcyv⟩
      · exact (hsnd (Fin.ext (hcxv.trans hcyv.symm))).elim
    apply hJ x.2 y.2 hxy
    rcases hbits with ⟨hcx, hcy⟩ | ⟨hcx, hcy⟩
    · rw [show x.1 = pairEquiv p cx from ((pairEquiv p).apply_symm_apply x.1).symm,
          show y.1 = pairEquiv p cy from ((pairEquiv p).apply_symm_apply y.1).symm,
          show cx = (cx.1, 0) from Prod.ext rfl hcx,
          show cy = (cx.1, 1) from Prod.ext hfst.symm hcy]
      exact pair_adj p hp cx.1
    · rw [show x.1 = pairEquiv p cx from ((pairEquiv p).apply_symm_apply x.1).symm,
          show y.1 = pairEquiv p cy from ((pairEquiv p).apply_symm_apply y.1).symm,
          show cx = (cx.1, 1) from Prod.ext rfl hcx,
          show cy = (cx.1, 0) from Prod.ext hfst.symm hcy]
      exact (pair_adj p hp cx.1).symm
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Fintype.card_fin] using hcard

theorem iterate_nextIndex (p : ℕ) (hp : 1 ≤ p) (i : Fin p) (m : ℕ) :
    (nextIndex p hp)^[m] i =
      ⟨(i.val + m) % p, Nat.mod_lt _ (by omega)⟩ := by
  induction m with
  | zero =>
      apply Fin.ext
      simp [Nat.mod_eq_of_lt i.isLt]
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih]
      apply Fin.ext
      simp only [nextIndex, Fin.val_mk]
      rw [← Nat.add_assoc]
      exact Nat.ModEq.add_right 1 (Nat.mod_modEq (i.val + m) p)

theorem exists_iterate_nextIndex_eq (p : ℕ) (hp : 1 ≤ p) (i j : Fin p) :
    ∃ m : ℕ, (nextIndex p hp)^[m] i = j := by
  refine ⟨p - i.val + j.val, ?_⟩
  rw [iterate_nextIndex]
  apply Fin.ext
  simp only
  have hi : i.val ≤ p := i.isLt.le
  rw [← Nat.add_assoc, Nat.add_sub_of_le hi, Nat.add_mod]
  simp [Nat.mod_eq_of_lt j.isLt]

/-- Equality in the even-cycle independence bound is rigid: the independent
set is one of the two alternating parity classes. -/
theorem independent_eq_alternating_of_card
    (p : ℕ) (hp : 1 ≤ p) (J : Finset (Fin (2 * p)))
    (hJ : (SimpleGraph.cycleGraph (2 * p)).IsIndepSet J)
    (hcard : J.card = p) : J = leftIndices p ∨ J = rightIndices p := by
  classical
  let f : {x // x ∈ J} → Fin p := fun x ↦ ((pairEquiv p).symm x.1).1
  have hf : Function.Injective f := by
    intro x y hxyfst
    apply Subtype.ext
    by_contra hxy
    let cx := (pairEquiv p).symm x.1
    let cy := (pairEquiv p).symm y.1
    have hfst : cx.1 = cy.1 := hxyfst
    have hsnd : cx.2 ≠ cy.2 := by
      intro hsnd
      apply hxy
      calc
        x.1 = pairEquiv p cx := ((pairEquiv p).apply_symm_apply x.1).symm
        _ = pairEquiv p cy := congrArg (pairEquiv p) (Prod.ext hfst hsnd)
        _ = y.1 := (pairEquiv p).apply_symm_apply y.1
    have hbits : (cx.2 = 0 ∧ cy.2 = 1) ∨ (cx.2 = 1 ∧ cy.2 = 0) := by
      have hcxv : cx.2.val = 0 ∨ cx.2.val = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega)
      have hcyv : cy.2.val = 0 ∨ cy.2.val = 1 :=
        Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega)
      rcases hcxv with hcxv | hcxv <;> rcases hcyv with hcyv | hcyv
      · exact (hsnd (Fin.ext (hcxv.trans hcyv.symm))).elim
      · exact Or.inl ⟨Fin.ext hcxv, Fin.ext hcyv⟩
      · exact Or.inr ⟨Fin.ext hcxv, Fin.ext hcyv⟩
      · exact (hsnd (Fin.ext (hcxv.trans hcyv.symm))).elim
    apply hJ x.2 y.2 hxy
    rcases hbits with ⟨hcx, hcy⟩ | ⟨hcx, hcy⟩
    · rw [show x.1 = pairEquiv p cx from ((pairEquiv p).apply_symm_apply x.1).symm,
          show y.1 = pairEquiv p cy from ((pairEquiv p).apply_symm_apply y.1).symm,
          show cx = (cx.1, 0) from Prod.ext rfl hcx,
          show cy = (cx.1, 1) from Prod.ext hfst.symm hcy]
      exact pair_adj p hp cx.1
    · rw [show x.1 = pairEquiv p cx from ((pairEquiv p).apply_symm_apply x.1).symm,
          show y.1 = pairEquiv p cy from ((pairEquiv p).apply_symm_apply y.1).symm,
          show cx = (cx.1, 1) from Prod.ext rfl hcx,
          show cy = (cx.1, 0) from Prod.ext hfst.symm hcy]
      exact (pair_adj p hp cx.1).symm
  have hcards : Fintype.card {x // x ∈ J} = Fintype.card (Fin p) := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using hcard
  have hsurj : Function.Surjective f :=
    ((Fintype.bijective_iff_injective_and_card f).2 ⟨hf, hcards⟩).2
  have hexact (i : Fin p) :
      pairEquiv p (i, 0) ∈ J ∨ pairEquiv p (i, 1) ∈ J := by
    obtain ⟨x, hx⟩ := hsurj i
    let cx := (pairEquiv p).symm x.1
    have hfst : cx.1 = i := hx
    have hbit : cx.2 = 0 ∨ cx.2 = 1 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (by omega : cx.2.val ≤ 1) with h | h
      · exact Or.inl (Fin.ext h)
      · exact Or.inr (Fin.ext h)
    rcases hbit with hbit | hbit
    · left
      have heq : x.1 = pairEquiv p (i, 0) := by
        calc
          x.1 = pairEquiv p cx := ((pairEquiv p).apply_symm_apply x.1).symm
          _ = pairEquiv p (i, 0) := congrArg (pairEquiv p) (Prod.ext hfst hbit)
      exact heq ▸ x.2
    · right
      have heq : x.1 = pairEquiv p (i, 1) := by
        calc
          x.1 = pairEquiv p cx := ((pairEquiv p).apply_symm_apply x.1).symm
          _ = pairEquiv p (i, 1) := congrArg (pairEquiv p) (Prod.ext hfst hbit)
      exact heq ▸ x.2
  have hprop {i : Fin p} (hi : pairEquiv p (i, 1) ∈ J) :
      pairEquiv p (nextIndex p hp i, 1) ∈ J := by
    rcases hexact (nextIndex p hp i) with hleft | hright
    · exact (hJ hi hleft (by
          intro heq
          exact (pair_next_adj p hp i).ne heq) (pair_next_adj p hp i)).elim
    · exact hright
  by_cases hnone : ∀ i : Fin p, pairEquiv p (i, 1) ∉ J
  · left
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨i, _hi, rfl⟩
      exact (hexact i).resolve_right (hnone i)
    · simp [leftIndices, hcard]
  · right
    push_neg at hnone
    obtain ⟨i, hi⟩ := hnone
    have hiter : ∀ m : ℕ, pairEquiv p ((nextIndex p hp)^[m] i, 1) ∈ J := by
      intro m
      induction m with
      | zero => simpa using hi
      | succ m ih =>
          rw [Function.iterate_succ_apply']
          exact hprop ih
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      rcases Finset.mem_map.mp hx with ⟨j, _hj, rfl⟩
      obtain ⟨m, hm⟩ := exists_iterate_nextIndex_eq p hp i j
      have hmemb := hiter m
      rw [hm] at hmemb
      exact hmemb
    · simp [rightIndices, hcard]

theorem left_right_disjoint (p : ℕ) :
    Disjoint (leftIndices p) (rightIndices p) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxL hxR
  rcases Finset.mem_map.mp hxL with ⟨i, _hi, rfl⟩
  rcases Finset.mem_map.mp hxR with ⟨j, _hj, heq⟩
  change pairEquiv p (j, 1) = pairEquiv p (i, 0) at heq
  have hpairs : (i, (0 : Fin 2)) = (j, (1 : Fin 2)) := by
    rw [← (pairEquiv p).symm_apply_apply (i, (0 : Fin 2)),
      ← (pairEquiv p).symm_apply_apply (j, (1 : Fin 2))]
    exact congrArg (pairEquiv p).symm heq.symm
  have : (0 : Fin 2) = 1 := congrArg Prod.snd hpairs
  exact Fin.zero_ne_one this

theorem leftIndices_card (p : ℕ) : (leftIndices p).card = p := by
  classical
  simp [leftIndices]

theorem rightIndices_card (p : ℕ) : (rightIndices p).card = p := by
  classical
  simp [rightIndices]

theorem leftIndices_independent (p : ℕ) (_hp : 1 ≤ p) :
    (SimpleGraph.cycleGraph (2 * p)).IsIndepSet (leftIndices p) := by
  classical
  let c := SimpleGraph.cycleGraph.bicoloring_of_even (2 * p)
    (show Even (2 * p) by refine ⟨p, ?_⟩; omega)
  have hc : (SimpleGraph.cycleGraph (2 * p)).IsIndepSet (c.colorClass true) := by
    intro a ha b hb _
    exact c.not_adj_of_mem_colorClass ha hb
  apply hc.mono
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨i, _hi, rfl⟩
  dsimp only [c, SimpleGraph.cycleGraph.bicoloring_of_even]
  change c (pairEquiv p (i, 0)) = true
  change decide ((pairEquiv p (i, 0)).val % 2 = 0) = true
  rw [pairEquiv_val]
  simp

theorem rightIndices_independent (p : ℕ) (_hp : 1 ≤ p) :
    (SimpleGraph.cycleGraph (2 * p)).IsIndepSet (rightIndices p) := by
  classical
  let c := SimpleGraph.cycleGraph.bicoloring_of_even (2 * p)
    (show Even (2 * p) by refine ⟨p, ?_⟩; omega)
  have hc : (SimpleGraph.cycleGraph (2 * p)).IsIndepSet (c.colorClass false) := by
    intro a ha b hb _
    exact c.not_adj_of_mem_colorClass ha hb
  apply hc.mono
  intro x hx
  rcases Finset.mem_map.mp hx with ⟨i, _hi, rfl⟩
  dsimp only [c, SimpleGraph.cycleGraph.bicoloring_of_even]
  change c (pairEquiv p (i, 1)) = false
  change decide ((pairEquiv p (i, 1)).val % 2 = 0) = false
  rw [pairEquiv_val]
  simp

/-- The canonical two alternating sides of an even cycle satisfy exactly the
abstract configuration used by the even-hole contraction argument. -/
theorem cycleGraph_configuration (p : ℕ) (hp : 2 ≤ p) :
    Erdos922.EvenHole.Configuration (SimpleGraph.cycleGraph (2 * p))
      (leftIndices p) (rightIndices p) p where
  disjoint := left_right_disjoint p
  two_le := hp
  card_left := leftIndices_card p
  card_right := rightIndices_card p
  indep_left := leftIndices_independent p (by omega)
  indep_right := rightIndices_independent p (by omega)
  cycle_bound := by
    intro I _hsub hI
    exact independent_card_le p (by omega) I hI
  cycle_eq_of_card := by
    intro I _hsub hI hcard
    exact independent_eq_alternating_of_card p (by omega) I hI hcard

/-- An abstract even-hole configuration transports along an induced graph
embedding.  The proof explicitly pulls every independent subset of the image
back through the embedding, so both the extremal bound and its equality case
are preserved. -/
theorem configuration_map_embedding
    {W : Type v} [Finite W] [DecidableEq W] [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V} (φ : H ↪g G)
    {A B : Finset W} {p : ℕ}
    (hC : Erdos922.EvenHole.Configuration H A B p) :
    Erdos922.EvenHole.Configuration G
      (A.map φ.toEmbedding) (B.map φ.toEmbedding) p := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  let e : W ↪ V := φ.toEmbedding
  have image_independent (S : Finset W) (hS : H.IsIndepSet S) :
      G.IsIndepSet (S.map e) := by
    intro x hx y hy hxy hGxy
    rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
    apply hS ha hb
    · intro hab
      subst b
      exact hxy rfl
    · exact φ.map_rel_iff.mp hGxy
  have pullback (I : Finset V)
      (hsub : I ⊆ A.map e ∪ B.map e) :
      ∃ J : Finset W, J ⊆ A ∪ B ∧ J.map e = I := by
    let J := (A ∪ B).filter fun a ↦ e a ∈ I
    refine ⟨J, Finset.filter_subset _ _, ?_⟩
    apply Finset.ext
    intro x
    constructor
    · intro hx
      rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
      exact (Finset.mem_filter.mp ha).2
    · intro hx
      have hxAB := hsub hx
      rw [← Finset.map_union] at hxAB
      rcases Finset.mem_map.mp hxAB with ⟨a, haAB, hax⟩
      apply Finset.mem_map.mpr
      refine ⟨a, Finset.mem_filter.mpr ⟨haAB, ?_⟩, hax⟩
      exact hax ▸ hx
  refine {
    disjoint := (Finset.disjoint_map e).2 hC.disjoint
    two_le := hC.two_le
    card_left := by simpa [e] using hC.card_left
    card_right := by simpa [e] using hC.card_right
    indep_left := image_independent A hC.indep_left
    indep_right := image_independent B hC.indep_right
    cycle_bound := ?_
    cycle_eq_of_card := ?_ }
  · intro I hsub hI
    obtain ⟨J, hJsub, hmap⟩ := pullback I hsub
    have hJind : H.IsIndepSet J := by
      intro a ha b hb hab hHab
      apply hI
      · rw [← hmap]
        exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
      · rw [← hmap]
        exact Finset.mem_map.mpr ⟨b, hb, rfl⟩
      · exact fun heq ↦ hab (e.injective heq)
      · exact φ.map_rel_iff.mpr hHab
    have hle := hC.cycle_bound J hJsub hJind
    rwa [← hmap, Finset.card_map] 
  · intro I hsub hI hcard
    obtain ⟨J, hJsub, hmap⟩ := pullback I hsub
    have hJind : H.IsIndepSet J := by
      intro a ha b hb hab hHab
      apply hI
      · rw [← hmap]
        exact Finset.mem_map.mpr ⟨a, ha, rfl⟩
      · rw [← hmap]
        exact Finset.mem_map.mpr ⟨b, hb, rfl⟩
      · exact fun heq ↦ hab (e.injective heq)
      · exact φ.map_rel_iff.mpr hHab
    have hJcard : J.card = p := by
      rw [← hcard, ← hmap, Finset.card_map]
    rcases hC.cycle_eq_of_card J hJsub hJind hJcard with hJA | hJB
    · left
      rw [← hmap, hJA]
    · right
      rw [← hmap, hJB]

/-- An induced copy of an even cycle in an ambient graph gives the exact
configuration needed by the contraction theorem. -/
theorem configuration_of_induced_even_cycle_iso
    [Finite V] [DecidableEq V] (G : SimpleGraph V) (C : Set V)
    (p : ℕ) (hp : 2 ≤ p)
    (e : G.induce C ≃g SimpleGraph.cycleGraph (2 * p)) :
    ∃ A B : Finset V, Erdos922.EvenHole.Configuration G A B p := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  let φ : SimpleGraph.cycleGraph (2 * p) ↪g G :=
    (SimpleGraph.Embedding.induce C).comp e.symm.toEmbedding
  refine ⟨(leftIndices p).map φ.toEmbedding,
    (rightIndices p).map φ.toEmbedding, ?_⟩
  exact configuration_map_embedding φ (cycleGraph_configuration p hp)

/-- An order-minimal counterexample contains no induced even cycle (stated
as an isomorphism onto an induced subgraph). -/
theorem no_induced_even_cycle_iso_of_no_configuration
    [Finite V] [DecidableEq V] (G : SimpleGraph V)
    (hnone : ¬ ∃ (A B : Finset V) (p : ℕ),
      Erdos922.EvenHole.Configuration G A B p) :
    ¬ ∃ (C : Set V) (p : ℕ), 2 ≤ p ∧
      Nonempty (G.induce C ≃g SimpleGraph.cycleGraph (2 * p)) := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  rintro ⟨C, p, hp, ⟨e⟩⟩
  obtain ⟨A, B, hC⟩ := configuration_of_induced_even_cycle_iso G C p hp e
  exact hnone ⟨A, B, p, hC⟩


end EvenCycleBridge

end Erdos922Recolor
