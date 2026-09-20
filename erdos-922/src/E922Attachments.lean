/-
Inherited Erdos922 attachment and shortest-cycle arguments.
Source plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos922.lean, SHA256
0bc22004ecbe76ab3cc3f263c29c76994b39017828ea835d987139fa324b9971.
Informal author: Jon Folkman. Formal authors: Codex; GPT-5.6 Sol.
Lean4.19 compatibility work by Codex/B under Gott-L's direction.
Private local research; upstream license unverified; no novelty claim.
-/
import E922AttachmentsCore
import E922AttachmentSupport
import E922SpanningCycleCompat

open SimpleGraph
open scoped ENat

namespace Erdos922Recolor
universe u
variable {V : Type u}


theorem isChordless_of_path_length_add_one_lt_shortest
    (G : SimpleGraph V) {n : ℕ} (hshort : IsShortestCycleLength G n)
    {a b : V} (P : G.Walk a b) (hP : P.IsPath)
    (hlen : P.length + 1 < n) : P.IsChordless := by
  classical
  rw [Walk.isChordless_iff_forall_mem_edges]
  intro x y hx hy hxy
  by_contra hnotedge
  have close_of_idx_le {x y : V}
      (hx : x ∈ P.support) (hy : y ∈ P.support) (hxy : G.Adj x y)
      (hnotedge : s(x, y) ∉ P.edges)
      (hidx : P.support.idxOf x ≤ P.support.idxOf y) : False := by
    let Q := P.dropUntil x hx
    have hyQ : y ∈ Q.support := by
      dsimp only [Q]
      rw [support_dropUntil_eq_drop_idxOf]
      have hylt := List.idxOf_lt_length_iff.mpr hy
      rw [List.mem_drop_iff_getElem]
      refine ⟨P.support.idxOf y - P.support.idxOf x, ?_, ?_⟩
      · rw [Walk.length_support]
        rw [Nat.sub_add_cancel hidx]
        simpa only [Walk.length_support] using hylt
      · have heq := List.getElem_idxOf hylt
        have hsum : P.support.idxOf x +
            (P.support.idxOf y - P.support.idxOf x) = P.support.idxOf y :=
          Nat.add_sub_of_le hidx
        have hopen : P.support[P.support.idxOf x +
            (P.support.idxOf y - P.support.idxOf x)]? = some y := by
          rw [hsum, List.getElem?_eq_getElem hylt, heq]
        exact (List.getElem?_eq_some_iff.mp hopen).2
    let S := Q.takeUntil y hyQ
    have hQ : Q.IsPath := hP.dropUntil hx
    have hS : S.IsPath := hQ.takeUntil hyQ
    have hedgeS : s(y, x) ∉ S.edges := by
      intro hmem
      apply hnotedge
      rw [Sym2.eq_swap]
      exact P.edges_dropUntil_subset hx
        (Q.edges_takeUntil_subset hyQ hmem)
    let d : G.Walk y y := S.cons hxy.symm
    have hd : d.IsCycle :=
      (Walk.cons_isCycle_iff S hxy.symm).2 ⟨hS, hedgeS⟩
    have hSle : S.length ≤ P.length :=
      (Q.length_takeUntil_le hyQ).trans (P.length_dropUntil_le hx)
    have hlower := hshort d hd
    change n ≤ S.length + 1 at hlower
    omega
  by_cases hidx : P.support.idxOf x ≤ P.support.idxOf y
  · exact close_of_idx_le hx hy hxy hnotedge hidx
  · have hidx' : P.support.idxOf y ≤ P.support.idxOf x := Nat.le_of_not_ge hidx
    have hswap : s(y, x) ∉ P.edges := by simpa only [Sym2.eq_swap] using hnotedge
    exact close_of_idx_le hy hx hxy.symm hswap hidx'

/-- A path inside an induced core, together with one outside vertex adjacent
to its distinct endpoints, closes up to a cycle two edges longer than the
path. -/
theorem exists_cycle_of_induced_path_and_two_neighbors
    (G : SimpleGraph V) {C : Set V} {r s : C} (hrs : r ≠ s)
    (P : (G.induce C).Walk r s) (hP : P.IsPath)
    {x : V} (hx : x ∉ C) (hrx : G.Adj r.1 x) (hsx : G.Adj s.1 x) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ c.length = P.length + 2 := by
  let P' := P.map (SimpleGraph.Embedding.induce (G := G) C).toHom
  have hP' : P'.IsPath :=
    Walk.map_isPath_of_injective (SimpleGraph.Embedding.induce (G := G) C).injective hP
  have hxP' : x ∉ P'.support := by
    intro hmem
    have hmem' : ∃ y ∈ P.support,
        (SimpleGraph.Embedding.induce (G := G) C).toHom y = x := by
      simpa only [P', Walk.support_map, List.mem_map] using hmem
    obtain ⟨y, _hy, hyx⟩ := hmem'
    have hyC : (SimpleGraph.Embedding.induce (G := G) C).toHom y ∈ C := y.2
    exact hx (hyx ▸ hyC)
  let Q : G.Walk x s.1 := P'.cons hrx.symm
  have hQ : Q.IsPath := hP'.cons hxP'
  have hPpos : 0 < P.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hrs (P.eq_of_length_eq_zero hzero)
  have hedge : s(s.1, x) ∉ Q.edges := by
    intro hmem
    have hone := hQ.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ hmem)
    have hQlen : Q.length = P.length + 1 := by
      change P'.length + 1 = P.length + 1
      dsimp only [P']
      rw [Walk.length_map]
    omega
  refine ⟨s.1, Q.cons hsx, ?_, ?_⟩
  · exact (Walk.cons_isCycle_iff Q hsx).2 ⟨hQ, hedge⟩
  · change Q.length + 1 = P.length + 2
    have hQlen : Q.length = P.length + 1 := by
      change P'.length + 1 = P.length + 1
      dsimp only [P']
      rw [Walk.length_map]
    omega

theorem exists_cycle_of_induced_path_and_attachment_edge
    (G : SimpleGraph V) {C : Set V} {r s : C} (hrs : r ≠ s)
    (P : (G.induce C).Walk r s) (hP : P.IsPath)
    {x y : V} (hx : x ∉ C) (hy : y ∉ C)
    (hrx : G.Adj r.1 x) (hxy : G.Adj x y) (hys : G.Adj y s.1) :
    ∃ (z : V) (c : G.Walk z z), c.IsCycle ∧ c.length = P.length + 3 := by
  let P' := P.map (SimpleGraph.Embedding.induce (G := G) C).toHom
  have hP' : P'.IsPath :=
    Walk.map_isPath_of_injective (SimpleGraph.Embedding.induce (G := G) C).injective hP
  have hxP' : x ∉ P'.support := by
    intro hmem
    have hmem' : ∃ t ∈ P.support,
        (SimpleGraph.Embedding.induce (G := G) C).toHom t = x := by
      simpa only [P', Walk.support_map, List.mem_map] using hmem
    obtain ⟨t, _ht, htx⟩ := hmem'
    exact hx (htx ▸ t.2)
  have hyP' : y ∉ P'.support := by
    intro hmem
    have hmem' : ∃ t ∈ P.support,
        (SimpleGraph.Embedding.induce (G := G) C).toHom t = y := by
      simpa only [P', Walk.support_map, List.mem_map] using hmem
    obtain ⟨t, _ht, hty⟩ := hmem'
    exact hy (hty ▸ t.2)
  have hyx : y ≠ x := hxy.ne.symm
  let Q : G.Walk x s.1 := P'.cons hrx.symm
  have hQ : Q.IsPath := hP'.cons hxP'
  have hyQ : y ∉ Q.support := by
    change y ∉ x :: P'.support
    intro hmem
    rcases (List.mem_cons.mp hmem) with h | h
    · exact hyx h
    · exact hyP' h
  let R : G.Walk y s.1 := Q.cons hxy.symm
  have hR : R.IsPath := hQ.cons hyQ
  have hPpos : 0 < P.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hrs (P.eq_of_length_eq_zero hzero)
  have hedge : s(s.1, y) ∉ R.edges := by
    intro hmem
    have hone := hR.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ hmem)
    have hRlen : R.length = P.length + 2 := by
      change P'.length + 2 = P.length + 2
      dsimp only [P']
      rw [Walk.length_map]
    omega
  refine ⟨s.1, R.cons hys.symm, ?_, ?_⟩
  · exact (Walk.cons_isCycle_iff R hys.symm).2 ⟨hR, hedge⟩
  · change R.length + 1 = P.length + 3
    change P'.length + 3 = P.length + 3
    dsimp only [P']
    rw [Walk.length_map]

/-- If the core path is chordless and each outside vertex has its indicated
endpoint as its unique neighbor in the core, the cycle closed through the
outside edge is chordless in the ambient graph. -/
theorem exists_chordless_cycle_of_induced_path_and_attachment_edge
    (G : SimpleGraph V) {C : Set V} {r s : C} (hrs : r ≠ s)
    (P : (G.induce C).Walk r s) (hP : P.IsPath) (hPchord : P.IsChordless)
    {x y : V} (hx : x ∉ C) (hy : y ∉ C)
    (hrx : G.Adj r.1 x) (hxy : G.Adj x y) (hys : G.Adj y s.1)
    (hxunique : ∀ t : C, t ≠ r → ¬ G.Adj t.1 x)
    (hyunique : ∀ t : C, t ≠ s → ¬ G.Adj t.1 y) :
    ∃ (z : V) (c : G.Walk z z),
      c.IsCycle ∧ c.IsChordless ∧ c.length = P.length + 3 := by
  let ι := (SimpleGraph.Embedding.induce (G := G) C).toHom
  let P' := P.map ι
  have hP' : P'.IsPath :=
    Walk.map_isPath_of_injective (SimpleGraph.Embedding.induce (G := G) C).injective hP
  have hxP' : x ∉ P'.support := by
    intro hmem
    have hmem' : ∃ t ∈ P.support, ι t = x := by
      simpa only [P', Walk.support_map, List.mem_map] using hmem
    obtain ⟨t, _ht, htx⟩ := hmem'
    exact hx (htx ▸ t.2)
  have hyP' : y ∉ P'.support := by
    intro hmem
    have hmem' : ∃ t ∈ P.support, ι t = y := by
      simpa only [P', Walk.support_map, List.mem_map] using hmem
    obtain ⟨t, _ht, hty⟩ := hmem'
    exact hy (hty ▸ t.2)
  let Q : G.Walk x s.1 := P'.cons hrx.symm
  have hQ : Q.IsPath := hP'.cons hxP'
  have hyQ : y ∉ Q.support := by
    change y ∉ x :: P'.support
    intro hmem
    rcases List.mem_cons.mp hmem with h | h
    · exact hxy.ne.symm h
    · exact hyP' h
  let R : G.Walk y s.1 := Q.cons hxy.symm
  have hR : R.IsPath := hQ.cons hyQ
  have hPpos : 0 < P.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hrs (P.eq_of_length_eq_zero hzero)
  have hedge : s(s.1, y) ∉ R.edges := by
    intro hmem
    have hone := hR.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ hmem)
    have hRlen : R.length = P.length + 2 := by
      change P'.length + 2 = P.length + 2
      dsimp only [P']
      rw [Walk.length_map]
    omega
  let d : G.Walk s.1 s.1 := R.cons hys.symm
  have hdcycle : d.IsCycle :=
    (Walk.cons_isCycle_iff R hys.symm).2 ⟨hR, hedge⟩
  have hsP' : s.1 ∈ P'.support := P'.end_mem_support
  have normalize_support {a : V} (ha : a ∈ d.support) :
      a = y ∨ a = x ∨ a ∈ P'.support := by
    change a ∈ s.1 :: y :: x :: P'.support at ha
    simp only [List.mem_cons] at ha
    rcases ha with ha | ha | ha | ha
    · exact Or.inr (Or.inr (ha ▸ hsP'))
    · exact Or.inl ha
    · exact Or.inr (Or.inl ha)
    · exact Or.inr (Or.inr ha)
  have core_preimage {a : V} (ha : a ∈ P'.support) :
      ∃ t : C, t ∈ P.support ∧ t.1 = a := by
    simp only [P', Walk.support_map, List.mem_map] at ha
    obtain ⟨t, ht, hta⟩ := ha
    exact ⟨t, ht, hta⟩
  have core_edge_mem {a b : V} (ha : a ∈ P'.support) (hb : b ∈ P'.support)
      (hab : G.Adj a b) : s(a, b) ∈ P'.edges := by
    obtain ⟨ta, hta, rfl⟩ := core_preimage ha
    obtain ⟨tb, htb, rfl⟩ := core_preimage hb
    have habC : (G.induce C).Adj ta tb := hab
    have hedgeP := hPchord.mem_edges hta htb habC
    change s(ι ta, ι tb) ∈ (P.map ι).edges
    rw [Walk.edges_map, List.mem_map]
    exact ⟨s(ta, tb), hedgeP, rfl⟩
  have hdchord : d.IsChordless := by
    rw [Walk.isChordless_iff_forall_mem_edges]
    intro a b ha hb hab
    have ha' := normalize_support ha
    have hb' := normalize_support hb
    change s(a, b) ∈ s(s.1, y) :: s(y, x) :: s(x, r.1) :: P'.edges
    simp only [List.mem_cons]
    rcases ha' with rfl | rfl | haC <;> rcases hb' with rfl | rfl | hbC
    · exact (hab.ne rfl).elim
    · exact Or.inr (Or.inl rfl)
    · obtain ⟨tb, htb, htbval⟩ := core_preimage hbC
      have htbs : tb = s := by
        apply Classical.byContradiction
        intro hne
        exact hyunique tb hne (htbval ▸ hab.symm)
      subst tb
      have hby : b = s.1 := htbval.symm
      subst b
      exact Or.inl Sym2.eq_swap
    · exact Or.inr (Or.inl Sym2.eq_swap)
    · exact (hab.ne rfl).elim
    · obtain ⟨tb, htb, htbval⟩ := core_preimage hbC
      have htbr : tb = r := by
        apply Classical.byContradiction
        intro hne
        exact hxunique tb hne (htbval ▸ hab.symm)
      subst tb
      have hbx : b = r.1 := htbval.symm
      subst b
      exact Or.inr (Or.inr (Or.inl rfl))
    · obtain ⟨ta, hta, htaval⟩ := core_preimage haC
      have htas : ta = s := by
        apply Classical.byContradiction
        intro hne
        exact hyunique ta hne (htaval ▸ hab)
      subst ta
      have hay : a = s.1 := htaval.symm
      subst a
      exact Or.inl rfl
    · obtain ⟨ta, hta, htaval⟩ := core_preimage haC
      have htar : ta = r := by
        apply Classical.byContradiction
        intro hne
        exact hxunique ta hne (htaval ▸ hab)
      subst ta
      have hax : a = r.1 := htaval.symm
      subst a
      exact Or.inr (Or.inr (Or.inl Sym2.eq_swap))
    · exact Or.inr (Or.inr (Or.inr (core_edge_mem haC hbC hab)))
  refine ⟨s.1, d, hdcycle, hdchord, ?_⟩
  change P'.length + 3 = P.length + 3
  dsimp only [P']
  rw [Walk.length_map]

/-- On a Hamiltonian cycle of length at least five, either of the two arcs
between distinct vertices can be chosen so that adding two edges still gives
a strictly shorter cycle. -/
theorem exists_short_arc_of_hamiltonian_cycle
    (G : SimpleGraph V) {C : Set V} {v : C}
    (c : (G.induce C).Walk v v) (hc : c.IsCycle)
    (hall : ∀ w : C, w ∈ c.support)
    {n : ℕ} (hcn : c.length = n) (hn : 5 ≤ n)
    (r s : C) (hrs : r ≠ s) :
    ∃ P : (G.induce C).Walk r s, P.IsPath ∧ P.length + 2 < n := by
  classical
  have hrmem : r ∈ c.support := hall r
  let cr : (G.induce C).Walk r r := c.rotate hrmem
  have hcr : cr.IsCycle := hc.rotate hrmem
  have hsmem : s ∈ cr.support :=
    (Walk.mem_support_rotate_iff c hrmem).2 (hall s)
  let P : (G.induce C).Walk r s := cr.takeUntil s hsmem
  let Q : (G.induce C).Walk s r := cr.dropUntil s hsmem
  have hP : P.IsPath := hcr.isPath_takeUntil hsmem
  have hPnot : ¬ P.Nil := by
    intro hnil
    exact hrs ((Walk.nil_takeUntil cr hsmem).mp hnil)
  have hpq : P.append Q = cr := Walk.take_spec cr hsmem
  have happ : (P.append Q).IsCycle := hpq ▸ hcr
  have hQ : Q.IsPath := happ.isPath_of_append_right hPnot
  have hsum : P.length + Q.length = n := by
    rw [← Walk.length_append, hpq]
    simpa [cr] using hcn
  by_cases hle : P.length ≤ Q.length
  · exact ⟨P, hP, by omega⟩
  · refine ⟨Q.reverse, hQ.reverse, ?_⟩
    simp only [Walk.length_reverse]
    omega

/-- An induced copy of the cycle graph supplies a spanning cycle walk in the
induced core. -/
theorem exists_spanning_cycle_of_induced_cycle_iso
    (G : SimpleGraph V) {C : Set V} {n : ℕ} (hn : 3 ≤ n)
    (e : G.induce C ≃g SimpleGraph.cycleGraph n) :
    ∃ (v : C) (c : (G.induce C).Walk v v),
      c.IsCycle ∧ c.length = n ∧ ∀ w : C, w ∈ c.support := by
  classical
  letI : Fintype C := Fintype.ofEquiv (Fin n) e.symm.toEquiv
  have hcopy : SimpleGraph.cycleGraph n ⊑ G.induce C := ⟨e.symm.toCopy⟩
  obtain ⟨v, c, hc, hcn⟩ :=
    (SimpleGraph.cycleGraph_isContained_iff (by omega)).mp hcopy
  have hcard : Fintype.card C = n := by
    simpa using e.card_eq
  have hall : ∀ w : C, w ∈ c.support :=
    hc.mem_support_of_length_eq_card (by simpa [hcard] using hcn)
  exact ⟨v, c, hc, hcn, hall⟩

/-- A vertex outside a shortest induced cycle of length at least five has at
most one neighbor on the cycle. -/
theorem shortestCycle_attachment_unique
    (G : SimpleGraph V) {C : Set V} {n : ℕ} (hn : 5 ≤ n)
    (e : G.induce C ≃g SimpleGraph.cycleGraph n)
    (hshort : IsShortestCycleLength G n) :
    ∀ {r s : C}, r ≠ s → ∀ {x : V}, x ∉ C →
      G.Adj s.1 x → ¬ G.Adj r.1 x := by
  intro r s hrs x hx hsx hrx
  obtain ⟨v, c, hc, hcn, hall⟩ :=
    exists_spanning_cycle_of_induced_cycle_iso G (by omega) e
  obtain ⟨P, hP, hPlt⟩ :=
    exists_short_arc_of_hamiltonian_cycle G c hc hall hcn hn r s hrs
  obtain ⟨z, d, hd, hdlen⟩ :=
    exists_cycle_of_induced_path_and_two_neighbors G hrs P hP hx hrx hsx
  have hlower := hshort d hd
  omega

/-- Reading a cycle walk at indices `0, ..., length - 1` maps every edge of
the standard cycle graph to an edge of the walk. -/
theorem adj_getVert_of_cycleGraph_adj
    {u : V} {G : SimpleGraph V} {p : G.Walk u u}
    (hp : p.IsCycle) {i j : Fin p.length}
    (hij : (SimpleGraph.cycleGraph p.length).Adj i j) :
    G.Adj (p.getVert i.val) (p.getVert j.val) := by
  have hn : 3 ≤ p.length := hp.three_le_length
  rw [SimpleGraph.cycleGraph_adj'] at hij
  rcases hij with hij | hij
  · by_cases hji : j ≤ i
    · have hval := Fin.coe_sub_iff_le.mpr hji
      rw [hval] at hij
      have heq : i.val = j.val + 1 := by omega
      rw [heq]
      exact (p.adj_getVert_succ (i := j.val) (by omega)).symm
    · have hijlt : i < j := lt_of_not_ge hji
      have hval := Fin.coe_sub_iff_lt.mpr hijlt
      rw [hval] at hij
      have hi : i.val = 0 := by omega
      have hj : j.val = p.length - 1 := by omega
      rw [hi, hj]
      have hadj := p.adj_getVert_succ (i := p.length - 1) (by omega)
      have hsum : p.length - 1 + 1 = p.length := by omega
      rw [hsum] at hadj
      simpa using hadj.symm
  · by_cases hijle : i ≤ j
    · have hval := Fin.coe_sub_iff_le.mpr hijle
      rw [hval] at hij
      have heq : j.val = i.val + 1 := by omega
      rw [heq]
      exact p.adj_getVert_succ (i := i.val) (by omega)
    · have hjilt : j < i := lt_of_not_ge hijle
      have hval := Fin.coe_sub_iff_lt.mpr hjilt
      rw [hval] at hij
      have hj : j.val = 0 := by omega
      have hi : i.val = p.length - 1 := by omega
      rw [hi, hj]
      have hadj := p.adj_getVert_succ (i := p.length - 1) (by omega)
      have hsum : p.length - 1 + 1 = p.length := by omega
      rw [hsum] at hadj
      simpa using hadj

/-- A chordless cycle walk is exactly an induced copy of the corresponding
standard cycle graph on the range of its non-repeated vertices. -/
theorem inducedCycleIso_of_chordless_cycle
    {u : V} {G : SimpleGraph V} (p : G.Walk u u)
    (hp : p.IsCycle) (hchord : p.IsChordless) :
    ∃ D : Set V, Nonempty
      (G.induce D ≃g SimpleGraph.cycleGraph p.length) := by
  let f0 : Fin p.length ↪ V := {
    toFun := fun i ↦ p.getVert i.val
    inj' := by
      intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn'
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega) hij }
  let f : SimpleGraph.cycleGraph p.length ↪g G := {
    __ := f0
    map_rel_iff' := by
      intro i j
      constructor
      · intro hG
        have hiS : p.getVert i.val ∈ p.support := p.getVert_mem_support _
        have hjS : p.getVert j.val ∈ p.support := p.getVert_mem_support _
        have hedge : s(p.getVert i.val, p.getVert j.val) ∈ p.edges :=
          hchord.mem_edges hiS hjS hG
        obtain ⟨k, hk, heq⟩ := (p.mk_mem_edges_iff_exists).mp hedge
        rcases Sym2.eq_iff.mp heq with hdir | hrev
        · have hik : i.val = k := by
            symm
            exact hp.getVert_injOn'
              (by simp only [Set.mem_setOf_eq]; omega)
              (by simp only [Set.mem_setOf_eq]; omega) hdir.1
          by_cases hks : k + 1 < p.length
          · have hjk : j.val = k + 1 := by
              symm
              exact hp.getVert_injOn'
                (by simp only [Set.mem_setOf_eq]; omega)
                (by simp only [Set.mem_setOf_eq]; omega) hdir.2
            rw [SimpleGraph.cycleGraph_adj']
            right
            rw [Fin.coe_sub_iff_le.mpr (by omega : i ≤ j)]
            omega
          · have hklen : k + 1 = p.length := by omega
            have hj0 : j.val = 0 := by
              have hv : p.getVert j.val = p.getVert 0 := by
                calc
                  p.getVert j.val = p.getVert (k + 1) := hdir.2.symm
                  _ = p.getVert p.length := congrArg p.getVert hklen
                  _ = p.getVert 0 := p.getVert_length.trans p.getVert_zero.symm
              exact hp.getVert_injOn'
                (by simp only [Set.mem_setOf_eq]; omega)
                (by simp only [Set.mem_setOf_eq]; omega) hv
            rw [SimpleGraph.cycleGraph_adj']
            right
            have hji : j < i := by
              rw [Fin.lt_def, hj0, hik]
              have hn := hp.three_le_length
              omega
            rw [Fin.coe_sub_iff_lt.mpr hji]
            rw [hj0, hik]
            have hn := hp.three_le_length
            omega
        · have hjk : j.val = k := by
            symm
            exact hp.getVert_injOn'
              (by simp only [Set.mem_setOf_eq]; omega)
              (by simp only [Set.mem_setOf_eq]; omega) hrev.1
          by_cases hks : k + 1 < p.length
          · have hik : i.val = k + 1 := by
              symm
              exact hp.getVert_injOn'
                (by simp only [Set.mem_setOf_eq]; omega)
                (by simp only [Set.mem_setOf_eq]; omega) hrev.2
            rw [SimpleGraph.cycleGraph_adj']
            left
            rw [Fin.coe_sub_iff_le.mpr (by omega : j ≤ i)]
            omega
          · have hklen : k + 1 = p.length := by omega
            have hi0 : i.val = 0 := by
              have hv : p.getVert i.val = p.getVert 0 := by
                calc
                  p.getVert i.val = p.getVert (k + 1) := hrev.2.symm
                  _ = p.getVert p.length := congrArg p.getVert hklen
                  _ = p.getVert 0 := p.getVert_length.trans p.getVert_zero.symm
              exact hp.getVert_injOn'
                (by simp only [Set.mem_setOf_eq]; omega)
                (by simp only [Set.mem_setOf_eq]; omega) hv
            rw [SimpleGraph.cycleGraph_adj']
            left
            have hij : i < j := by
              rw [Fin.lt_def, hi0, hjk]
              have hn := hp.three_le_length
              omega
            rw [Fin.coe_sub_iff_lt.mpr hij]
            rw [hi0, hjk]
            have hn := hp.three_le_length
            omega
      · exact adj_getVert_of_cycleGraph_adj hp }
  let er : SimpleGraph.cycleGraph p.length ≃g G.induce (Set.range f) := {
    __ := Equiv.ofInjective f f.injective
    map_rel_iff' := by
      intro i j
      exact f.map_rel_iff }
  exact ⟨Set.range f, ⟨er.symm⟩⟩


def NoInducedEvenCycleIso (G : SimpleGraph V) : Prop :=
  ¬ ∃ (D : Set V) (p : ℕ), 2 ≤ p ∧
    Nonempty (G.induce D ≃g SimpleGraph.cycleGraph (2 * p))

/-- Under induced-even-cycle exclusion, no chordless cycle walk can have
even length. -/
theorem not_even_length_of_chordless_cycle
    (G : SimpleGraph V) (hno : NoInducedEvenCycleIso G)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hchord : c.IsChordless) :
    ¬ Even c.length := by
  rintro ⟨p, hpLen⟩
  have hlen : c.length = 2 * p := by omega
  have hp : 2 ≤ p := by
    have := hc.three_le_length
    omega
  obtain ⟨D, ⟨e⟩⟩ := inducedCycleIso_of_chordless_cycle c hc hchord
  apply hno
  refine ⟨D, p, hp, ?_⟩
  rw [hlen] at e
  exact ⟨e⟩

/-- The final local anticompleteness argument, isolated from the construction
of the odd arc: an odd chordless core path between two attachment vertices,
together with an edge between their outside neighbors, closes to a forbidden
even chordless cycle. -/
theorem attachments_anticomplete_of_odd_chordless_connectors
    (G : SimpleGraph V) (C : Set V)
    (hno : NoInducedEvenCycleIso G)
    (hunique : ∀ {r s : C}, r ≠ s → ∀ {x : V}, x ∉ C →
      G.Adj s.1 x → ¬ G.Adj r.1 x)
    (hconnector : ∀ (r s : C), r ≠ s →
      ∃ P : (G.induce C).Walk r s,
        P.IsPath ∧ P.IsChordless ∧ Odd P.length) :
    ∀ {r s : C}, r ≠ s → ∀ {x y : V}, x ∉ C → y ∉ C →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y := by
  intro r s hrs x y hx hy hrx hsy hxy
  obtain ⟨P, hP, hPchord, hPodd⟩ := hconnector r s hrs
  have hxunique : ∀ t : C, t ≠ r → ¬ G.Adj t.1 x := by
    intro t htr
    exact hunique htr hx hrx
  have hyunique : ∀ t : C, t ≠ s → ¬ G.Adj t.1 y := by
    intro t hts
    exact hunique hts hy hsy
  obtain ⟨z, d, hdcycle, hdchord, hdlen⟩ :=
    exists_chordless_cycle_of_induced_path_and_attachment_edge
      G hrs P hP hPchord hx hy hrx hxy hsy.symm hxunique hyunique
  apply not_even_length_of_chordless_cycle G hno d hdcycle hdchord
  obtain ⟨m, hm⟩ := hPodd
  refine ⟨m + 2, ?_⟩
  omega

/-- Attachment sets at distinct vertices of a shortest induced odd cycle are
anticomplete when induced even cycles are excluded. -/
theorem shortestOddCycle_attachments_anticomplete
    (G : SimpleGraph V) {C : Set V} {n : ℕ}
    (hn : 5 ≤ n) (hnOdd : Odd n)
    (e : G.induce C ≃g SimpleGraph.cycleGraph n)
    (hshort : IsShortestCycleLength G n)
    (hno : NoInducedEvenCycleIso G)
    (hunique : ∀ {r s : C}, r ≠ s → ∀ {x : V}, x ∉ C →
      G.Adj s.1 x → ¬ G.Adj r.1 x) :
    ∀ {r s : C}, r ≠ s → ∀ {x y : V}, x ∉ C → y ∉ C →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y := by
  classical
  intro r s hrs x y hx hy hrx hsy hxy
  obtain ⟨v, c, hc, hcn, hall⟩ :=
    exists_spanning_cycle_of_induced_cycle_iso G (by omega) e
  have hrmem : r ∈ c.support := hall r
  let cr : (G.induce C).Walk r r := c.rotate hrmem
  have hcr : cr.IsCycle := hc.rotate hrmem
  have hsmem : s ∈ cr.support :=
    (Walk.mem_support_rotate_iff c hrmem).2 (hall s)
  let P : (G.induce C).Walk r s := cr.takeUntil s hsmem
  let Q : (G.induce C).Walk s r := cr.dropUntil s hsmem
  let QR : (G.induce C).Walk r s := Q.reverse
  have hP : P.IsPath := hcr.isPath_takeUntil hsmem
  have hPnot : ¬ P.Nil := by
    intro hnil
    exact hrs ((Walk.nil_takeUntil cr hsmem).mp hnil)
  have hpq : P.append Q = cr := Walk.take_spec cr hsmem
  have happ : (P.append Q).IsCycle := hpq ▸ hcr
  have hQ : Q.IsPath := happ.isPath_of_append_right hPnot
  have hQR : QR.IsPath := hQ.reverse
  have hsum : P.length + QR.length = n := by
    simp only [QR, Walk.length_reverse]
    rw [← Walk.length_append, hpq]
    simpa [cr] using hcn
  have hPpos : 0 < P.length := by
    rw [Walk.not_nil_iff_lt_length] at hPnot
    exact hPnot
  have hQRpos : 0 < QR.length := by
    apply Nat.pos_of_ne_zero
    intro hz
    have heq : r = s := QR.eq_of_length_eq_zero hz
    exact hrs heq
  obtain ⟨zP, dP, hdP, hdPlen⟩ :=
    exists_cycle_of_induced_path_and_attachment_edge
      G hrs P hP hx hy hrx hxy hsy.symm
  obtain ⟨zQ, dQ, hdQ, hdQlen⟩ :=
    exists_cycle_of_induced_path_and_attachment_edge
      G hrs QR hQR hx hy hrx hxy hsy.symm
  have hlowerP := hshort dP hdP
  have hlowerQ := hshort dQ hdQ
  have hn5 : n = 5 := by
    obtain ⟨t, ht⟩ := hnOdd
    omega
  have hlengths :
      (P.length = 3 ∧ QR.length = 2) ∨
      (P.length = 2 ∧ QR.length = 3) := by
    omega
  have hshortC : IsShortestCycleLength (G.induce C) n := by
    intro w d hd
    let dm := d.map (SimpleGraph.Embedding.induce (G := G) C).toHom
    have hdm : dm.IsCycle :=
      hd.map (SimpleGraph.Embedding.induce (G := G) C).injective
    have hlower := hshort dm hdm
    simpa only [dm, Walk.length_map] using hlower
  have hxunique : ∀ t : C, t ≠ r → ¬ G.Adj t.1 x := by
    intro t htr
    exact hunique htr hx hrx
  have hyunique : ∀ t : C, t ≠ s → ¬ G.Adj t.1 y := by
    intro t hts
    exact hunique hts hy hsy
  rcases hlengths with ⟨hP3, _hQR2⟩ | ⟨_hP2, hQR3⟩
  · have hPchord : P.IsChordless :=
      isChordless_of_path_length_add_one_lt_shortest
        (G.induce C) hshortC P hP (by omega)
    obtain ⟨z, d, hd, hdchord, hdlen⟩ :=
      exists_chordless_cycle_of_induced_path_and_attachment_edge
        G hrs P hP hPchord hx hy hrx hxy hsy.symm hxunique hyunique
    exact not_even_length_of_chordless_cycle G hno d hd hdchord ⟨3, by omega⟩
  · have hQRchord : QR.IsChordless :=
      isChordless_of_path_length_add_one_lt_shortest
        (G.induce C) hshortC QR hQR (by omega)
    obtain ⟨z, d, hd, hdchord, hdlen⟩ :=
      exists_chordless_cycle_of_induced_path_and_attachment_edge
        G hrs QR hQR hQRchord hx hy hrx hxy hsy.symm hxunique hyunique
    exact not_even_length_of_chordless_cycle G hno d hd hdchord ⟨3, by omega⟩

end Erdos922Recolor
