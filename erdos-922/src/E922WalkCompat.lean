import Mathlib.Combinatorics.SimpleGraph.Path

/-!
Lean4.19 compatibility lemmas needed by the public Folkman/Erdos922 proof.
These proofs are written locally by Codex under Gott-L's direction, using
existing Mathlib4.19 definitions. Folkman's mathematics and the public finite
formalization credited to Codex/GPT-5.6 Sol are not claimed as new work.
No theorem below postulates the finite Folkman conclusion.
-/

namespace SimpleGraph.Walk

universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Contiguous walk containment, expressed by an actual prefix and suffix. -/
def IsSubwalk {a b c d : V} (q : G.Walk c d) (p : G.Walk a b) : Prop :=
  ∃ (r : G.Walk a c) (s : G.Walk d b), p = r.append (q.append s)

theorem length_le_of_isSubwalk {a b c d : V} {q : G.Walk c d} {p : G.Walk a b}
    (h : q.IsSubwalk p) : q.length ≤ p.length := by
  obtain ⟨r, s, rfl⟩ := h
  simp only [length_append]
  omega

theorem isPath_iff_isSubwalk_imp_nil {a b : V} {p : G.Walk a b} :
    p.IsPath ↔ ∀ (x : V) (q : G.Walk x x), q.IsSubwalk p → q.Nil := by
  classical
  constructor
  · intro hp x q hq
    obtain ⟨r, s, rfl⟩ := hq
    exact nil_iff_eq_nil.mpr (isPath_iff_eq_nil q |>.mp
      (hp.of_append_right.of_append_left))
  · intro h
    induction p with
    | nil => exact IsPath.nil
    | @cons a c b hac p ih =>
      apply (cons_isPath_iff hac p).mpr
      constructor
      · apply ih
        intro x q hq
        obtain ⟨r, s, he⟩ := hq
        apply h x q
        refine ⟨r.cons hac, s, ?_⟩
        simp only [cons_append, he]
      · intro ha
        let q : G.Walk a a := (p.takeUntil a ha).cons hac
        have hq : q.IsSubwalk (p.cons hac) := by
          refine ⟨nil, p.dropUntil a ha, ?_⟩
          simp only [nil_append, q, cons_append, take_spec]
        exact not_nil_cons (h a q hq)

theorem IsPath.not_mem_endpoint_edge_of_two_le {a b : V} {p : G.Walk a b}
    (hp : p.IsPath) (hlen : 2 ≤ p.length) : s(a, b) ∉ p.edges := by
  cases p with
  | nil => simp at hlen
  | @cons a c b hac p =>
    obtain ⟨hp, ha⟩ := (cons_isPath_iff hac p).mp hp
    intro he
    simp only [edges_cons, List.mem_cons] at he
    rcases he with he | he
    · have hbc : b = c := by
        rcases Sym2.eq_iff.mp he with h | h
        · exact h.2
        · exact h.2.trans h.1
      subst b
      have hnil := (isPath_iff_eq_nil p).mp hp
      simp [hnil] at hlen
    · exact ha (p.fst_mem_support_of_mem_edges he)

theorem isCycle_iff_isPath_tail_and_le_length {a : V} {p : G.Walk a a} :
    p.IsCycle ↔ p.tail.IsPath ∧ 3 ≤ p.length := by
  constructor
  · intro hp
    refine ⟨?_, hp.three_le_length⟩
    cases p with
    | nil => exact (hp.ne_nil rfl).elim
    | cons h p => simpa using ((cons_isCycle_iff p h).mp hp).1
  · rintro ⟨hp, hlen⟩
    cases p with
    | nil => simp at hlen
    | cons h p =>
      have hp' : p.IsPath := by simpa using hp
      apply (cons_isCycle_iff p h).mpr
      refine ⟨hp', ?_⟩
      rw [Sym2.eq_swap]
      exact hp'.not_mem_endpoint_edge_of_two_le (by simp only [length_cons] at hlen; omega)

end SimpleGraph.Walk
