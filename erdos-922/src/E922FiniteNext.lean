/-
Inherited public Folkman proof, plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos922.lean original lines808--1037.
Original mathematics: Jon Folkman. Original formal authors: Codex; GPT-5.6 Sol.
Local Lean4.19 compatibility integration under Gott-L's direction, by Codex/B.
Retains public statements and arguments; no final finite Folkman supplier claim.
Private local experiment; upstream license has not yet been independently pinned.
-/
import E922FinitePrelim
import E922CycleCompat
import E922AcyclicCompat

open SimpleGraph
open scoped ENat

namespace Erdos922FullB
universe u

/-- Hence a minimal counterexample is not acyclic, since every finite
acyclic simple graph is two-colorable. -/
theorem IsOrderMinimalCounterexample.not_isAcyclic
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) : ¬ G.IsAcyclic := by
  intro hacyclic
  exact hG.not_colorable_two hacyclic.colorable_two

/-- A minimal counterexample therefore contains a cycle realizing the
girth.  This packages exactly the shortest-cycle data used by the structural
part of Folkman's proof. -/
theorem IsOrderMinimalCounterexample.exists_shortest_cycle
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) :
    ∃ v, ∃ w : G.Walk v v, w.IsCycle ∧ w.length = G.girth := by
  obtain ⟨v, w, hwcycle, hlength⟩ := (SimpleGraph.exists_girth_eq_length (G := G)).mpr hG.not_isAcyclic
  exact ⟨v, w, hwcycle, hlength.symm⟩

/-- Equivalently, failure of two-colorability directly supplies an odd
closed walk.  Extracting an odd simple cycle from this walk is one possible
route to the base case; the modern proof instead takes a shortest cycle and
uses the previously established absence of even holes. -/
theorem IsOrderMinimalCounterexample.exists_odd_closed_walk
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) :
    ∃ v, ∃ w : G.Walk v v, Odd w.length := by
  have hnot := hG.not_colorable_two
  rw [SimpleGraph.two_colorable_iff_forall_loop_even] at hnot
  push_neg at hnot
  obtain ⟨v, w, hw⟩ := hnot
  exact ⟨v, w, Nat.not_even_iff_odd.mp hw⟩

/-- Once the girth-realizing cycle is known to be odd (in Folkman's
argument this follows from chordlessness and the exclusion of induced even
cycles), it witnesses positive hereditary deficiency. -/
theorem IsOrderMinimalCounterexample.fOn_pos_of_girth_odd
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) (hodd : Odd G.girth) :
    0 < fOn G Finset.univ := by
  classical
  obtain ⟨v, w, hwcycle, hlength⟩ := hG.exists_shortest_cycle
  have hthree : 3 ≤ G.girth := by
    rw [← hlength]
    exact hwcycle.three_le_length
  have hcopy : SimpleGraph.cycleGraph G.girth ⊑ G := by
    rw [SimpleGraph.cycleGraph_isContained_iff (by omega)]
    exact ⟨v, w, hwcycle, hlength⟩
  obtain ⟨c⟩ := hcopy
  exact fOn_pos_of_odd_cycle_copy G hthree hodd c

/-- The positive deficiency raises the automatic lower bound on the
chromatic number from three to four. -/
theorem IsOrderMinimalCounterexample.four_le_chiNat_of_girth_odd
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) (hodd : Odd G.girth) :
    4 ≤ chiNat G := by
  classical
  exact four_le_chiNat_of_not_folkmanBound_of_fOn_pos G hG.counterexample
    (hG.fOn_pos_of_girth_odd hodd)

/-- Every odd closed walk in a simple graph contains an odd simple cycle.
The proof recursively removes a nontrivial closed subwalk of the tail.  If
that subwalk is odd we recurse into it; if it is even we delete it, preserving
odd parity and strictly decreasing length. -/
theorem exists_odd_cycle_of_odd_closed_walk
    {V : Type u} {G : SimpleGraph V} {v : V}
    (w : G.Walk v v) (hodd : Odd w.length) :
    ∃ x, ∃ c : G.Walk x x, c.IsCycle ∧ Odd c.length := by
  classical
  have hwnnil : ¬ w.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    obtain ⟨m, hm⟩ := hodd
    omega
  by_cases hpath : w.tail.IsPath
  · have hnotone : w.length ≠ 1 := by
      intro hone
      exact (G.ne_of_adj (w.adj_of_length_eq_one hone)) rfl
    have hthree : 3 ≤ w.length := by
      obtain ⟨m, hm⟩ := hodd
      omega
    exact ⟨v, w, Walk.isCycle_iff_isPath_tail_and_le_length.mpr
      ⟨hpath, hthree⟩, hodd⟩
  · rw [Walk.isPath_iff_isSubwalk_imp_nil] at hpath
    push_neg at hpath
    obtain ⟨x, q, hqsub, hqnonnil⟩ := hpath
    have hqlt : q.length < w.length := by
      have hle := Walk.length_le_of_isSubwalk hqsub
      have htail : w.tail.length < w.length := by
        have := Walk.length_tail_add_one hwnnil
        omega
      exact hle.trans_lt htail
    by_cases hqeven : Even q.length
    · obtain ⟨ru, rv, hdecomp⟩ := hqsub
      let r : G.Walk v v :=
        Walk.cons (w.adj_snd hwnnil) (ru.append rv)
      have hlen : w.length = r.length + q.length := by
        have htail_len := Walk.length_tail_add_one hwnnil
        rw [hdecomp, Walk.length_append, Walk.length_append] at htail_len
        simp only [r, Walk.length_cons, Walk.length_append]
        omega
      have hrodd : Odd r.length := by
        apply Nat.not_even_iff_odd.mp
        intro hreven
        apply (Nat.not_even_iff_odd.mpr hodd)
        rw [hlen]
        exact hreven.add hqeven
      have hrlt : r.length < w.length := by
        have hqpos : 0 < q.length := by
          rw [← Walk.not_nil_iff_lt_length]
          exact hqnonnil
        omega
      exact exists_odd_cycle_of_odd_closed_walk r hrodd
    · exact exists_odd_cycle_of_odd_closed_walk q
        (Nat.not_even_iff_odd.mp hqeven)
termination_by w.length
decreasing_by
  · simpa only [r, Walk.length_cons, Walk.length_append] using hrlt
  · exact hqlt

/-- The direct odd-cycle consequence of failure of two-colorability. -/
theorem IsOrderMinimalCounterexample.exists_odd_cycle
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) :
    ∃ x, ∃ c : G.Walk x x, c.IsCycle ∧ Odd c.length := by
  classical
  obtain ⟨v, w, hodd⟩ := hG.exists_odd_closed_walk
  exact exists_odd_cycle_of_odd_closed_walk w hodd

/-- Unconditional positivity of the hereditary deficiency maximum for an
order-minimal counterexample. -/
theorem IsOrderMinimalCounterexample.fOn_pos
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) : 0 < fOn G Finset.univ := by
  classical
  obtain ⟨v, c, hcycle, hodd⟩ := hG.exists_odd_cycle
  have hcopy : SimpleGraph.cycleGraph c.length ⊑ G := by
    rw [SimpleGraph.cycleGraph_isContained_iff (by
      exact Nat.lt_of_lt_of_le (by omega) hcycle.three_le_length)]
    exact ⟨v, c, hcycle, rfl⟩
  obtain ⟨copy⟩ := hcopy
  exact fOn_pos_of_odd_cycle_copy G hcycle.three_le_length hodd copy

/-- Every order-minimal counterexample has natural chromatic number at
least four. -/
theorem IsOrderMinimalCounterexample.four_le_chiNat
    {V : Type u} [Fintype V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G) : 4 ≤ chiNat G := by
  classical
  exact four_le_chiNat_of_not_folkmanBound_of_fOn_pos G hG.counterexample hG.fOn_pos


/-- The remaining structural target in a strong-induction proof: there is no
vertex-order-minimal counterexample.  This is a proposition, not a postulate;
the even-hole, diamond, and recoloring development must prove it. -/
noncomputable def NoOrderMinimalCounterexample : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    ¬ IsOrderMinimalCounterexample G

/-- Strong-induction assembly: once the structural argument excludes every
order-minimal counterexample, Folkman's bound holds for every finite graph. -/
theorem folkmanBound_of_noOrderMinimalCounterexample
    (hNo : NoOrderMinimalCounterexample.{u}) :
    ∀ {V : Type u} [Fintype V] (G : SimpleGraph V),
      FolkmanBound G := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ (V : Type u) [Fintype V] [DecidableEq V], Fintype.card V = n →
      ∀ G : SimpleGraph V, FolkmanBound G
  have hall : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp only [P]
        intro V _ _ hV G
        by_contra hbad
        apply hNo G
        refine ⟨hbad, ?_⟩
        intro W _ _ H hWV
        apply ih (Fintype.card W)
        · omega
        · rfl
  intro V _ G
  exact hall (Fintype.card V) V rfl G

/-- Numerical form of the critical split property `(A)` in the modern proof
of Folkman's theorem.  The two hypotheses are precisely what a least-order
counterexample supplies: the current graph violates the bound, while both
proper induced sides satisfy it.

Using `fOn` keeps all potentials on the ambient vertex type. -/
theorem critical_split_inequality
    {V : Type u} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hcounter : fOn G Finset.univ + 2 < (chiNat G : ℤ))
    (hminimal : ∀ S : Finset V, S ⊂ (Finset.univ : Finset V) →
      (chiNat (G.induce (S : Set V)) : ℤ) ≤ fOn G S + 2)
    (X : Finset V) (hXnonempty : X.Nonempty) (hXne : X ≠ Finset.univ) :
    chiNat (G.induce (X : Set V)) +
        chiNat (G.induce ((↑(Xᶜ) : Set V))) ≤ chiNat G + 1 := by
  classical
  have hXproper : X ⊂ (Finset.univ : Finset V) :=
    (Finset.subset_univ X).ssubset_of_ne hXne
  have hcomp_ne : (Xᶜ : Finset V) ≠ Finset.univ := by
    exact (Finset.compl_ne_univ_iff_nonempty X).mpr hXnonempty
  have hcompproper : (Xᶜ : Finset V) ⊂ (Finset.univ : Finset V) :=
    (Finset.subset_univ Xᶜ).ssubset_of_ne hcomp_ne
  have hleft := hminimal X hXproper
  have hright := hminimal Xᶜ hcompproper
  have hdisj : Disjoint X Xᶜ := disjoint_compl_right
  have hpot := fOn_add_le_fOn_union G hdisj
  have hunion : X ∪ Xᶜ = (Finset.univ : Finset V) := Finset.union_compl X
  rw [hunion] at hpot
  have hgap : fOn G Finset.univ + 3 ≤ (chiNat G : ℤ) := by omega
  norm_cast
  norm_cast at hleft hright hcounter hpot hgap
  omega

/-- Property `(A)` for an actual vertex-order-minimal counterexample. -/
theorem IsOrderMinimalCounterexample.critical_split
    {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : IsOrderMinimalCounterexample G)
    (X : Finset V) (hXnonempty : X.Nonempty) (hXne : X ≠ Finset.univ) :
    chiNat (G.induce (X : Set V)) +
        chiNat (G.induce ((↑(Xᶜ) : Set V))) ≤ chiNat G + 1 := by
  apply critical_split_inequality G (counterexample_gap_int G hG.counterexample)
  · intro S hS
    exact hG.proper_induce_chiNat_le S hS
  · exact hXnonempty
  · exact hXne

end Erdos922FullB
