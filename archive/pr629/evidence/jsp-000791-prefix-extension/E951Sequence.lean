/-
Copyright 2026. Released under the Apache License, Version 2.0.
Gott-L: project planning. Codex: Lean implementation.
Coherent finite-prefix recursion and its finitely supported exponent bridge.
The analytic one-step existence statement remains an explicit hypothesis here.
-/
import E951Append
import Mathlib.Algebra.BigOperators.Finsupp.Basic

set_option warningAsError true

open scoped BigOperators

namespace E951

def ExtensionStep : Prop :=
  ∀ {n : ℕ} (a : Fin n → ℝ), (∀ i, 1 < a i) → Separated a →
    ∀ B : ℝ, ∃ x, B < x ∧ 1 < x ∧ Separated (Fin.snoc a x)

structure GoodPrefix (n : ℕ) where
  val : Fin n → ℝ
  positive : ∀ i, 1 < val i
  increasing : StrictMono val
  separated : Separated val

private theorem snoc_strictMono {n : ℕ} (a : Fin n → ℝ) (x : ℝ)
    (ha : StrictMono a) (hx : ∀ i, a i < x) : StrictMono (Fin.snoc a x) := by
  intro i j
  refine Fin.lastCases ?_ (fun i' => ?_) i
  · refine Fin.lastCases ?_ (fun j' => ?_) j
    · intro hij
      exact False.elim (lt_irrefl _ hij)
    · intro hij
      exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
  · refine Fin.lastCases ?_ (fun j' => ?_) j
    · intro _
      simpa using hx i'
    · intro hij
      simpa using ha (show i' < j' from hij)

noncomputable def extendPrefix (hstep : ExtensionStep) {n : ℕ}
    (p : GoodPrefix n) : GoodPrefix (n + 1) := by
  classical
  let h := hstep p.val p.positive p.separated (∑ i, p.val i)
  let x := Classical.choose h
  have hx := Classical.choose_spec h
  refine ⟨Fin.snoc p.val x, ?_, snoc_strictMono p.val x p.increasing ?_, hx.2.2⟩
  · intro i
    exact Fin.lastCases (by simpa using hx.2.1)
      (fun j => by simpa using p.positive j) i
  · intro i
    have hi : p.val i ≤ ∑ j, p.val j := Finset.single_le_sum
      (fun j _ => le_of_lt (lt_trans zero_lt_one (p.positive j))) (Finset.mem_univ i)
    exact hi.trans_lt hx.1

@[simp] theorem extendPrefix_old (hstep : ExtensionStep) {n : ℕ}
    (p : GoodPrefix n) (i : Fin n) :
    (extendPrefix hstep p).val i.castSucc = p.val i := by
  simp [extendPrefix]

noncomputable def prefixChain (hstep : ExtensionStep) {n : ℕ}
    (p : GoodPrefix n) : (t : ℕ) → GoodPrefix (n + t)
  | 0 => p
  | t + 1 => extendPrefix hstep (prefixChain hstep p t)

theorem prefixChain_stable (hstep : ExtensionStep) {n : ℕ} (p : GoodPrefix n)
    {t s : ℕ} (hts : t ≤ s) (i : Fin (n + t)) :
    (prefixChain hstep p s).val ⟨i.val, by omega⟩ =
      (prefixChain hstep p t).val i := by
  induction s, hts using Nat.le_induction with
  | base => rfl
  | succ s hts ih =>
    change (extendPrefix hstep (prefixChain hstep p s)).val
      (Fin.castSucc ⟨i.val, by omega⟩) = _
    rw [extendPrefix_old]
    exact ih

noncomputable def limitSequence (hstep : ExtensionStep) {n : ℕ}
    (p : GoodPrefix n) (i : ℕ) : ℝ :=
  (prefixChain hstep p (i + 1)).val ⟨i, by omega⟩

theorem limitSequence_agrees (hstep : ExtensionStep) {n : ℕ} (p : GoodPrefix n)
    (t : ℕ) (i : Fin (n + t)) :
    limitSequence hstep p i = (prefixChain hstep p t).val i := by
  let s := max t (i.val + 1)
  have ht : t ≤ s := le_max_left _ _
  have hi : i.val + 1 ≤ s := le_max_right _ _
  have h₁ := prefixChain_stable hstep p ht i
  have h₂ := prefixChain_stable hstep p hi (⟨i.val, by omega⟩ : Fin (n + (i.val + 1)))
  exact h₂.symm.trans h₁

theorem limitSequence_strictMono (hstep : ExtensionStep) {n : ℕ}
    (p : GoodPrefix n) : StrictMono (limitSequence hstep p) := by
  intro i j hij
  rw [limitSequence_agrees hstep p (j + 1) (⟨i, by omega⟩ : Fin (n + (j + 1))),
    limitSequence_agrees hstep p (j + 1) (⟨j, by omega⟩ : Fin (n + (j + 1)))]
  exact (prefixChain hstep p (j + 1)).increasing hij

theorem sequenceMonomial_eq_prefix (a : ℕ → ℝ) (u : ℕ →₀ ℕ) (N : ℕ)
    (hu : u.support ⊆ Finset.range N) :
    sequenceMonomial a u = monomial (fun i : Fin N => a i) (fun i => u i) := by
  classical
  unfold sequenceMonomial monomial
  rw [Finsupp.prod_of_support_subset u hu (fun i k => a i ^ k) (by simp)]
  exact (Fin.prod_univ_eq_prod_range (fun i => a i ^ u i) N).symm

theorem sequenceSeparated_of_prefixes (a : ℕ → ℝ)
    (hs : ∀ N, Separated (fun i : Fin N => a i)) : SequenceSeparated a := by
  classical
  intro u v huv
  let N := (u.support ∪ v.support).sup id + 1
  have hb : u.support ∪ v.support ⊆ Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
  have hu : u.support ⊆ Finset.range N := Finset.Subset.trans Finset.subset_union_left hb
  have hv : v.support ⊆ Finset.range N := Finset.Subset.trans Finset.subset_union_right hb
  rw [sequenceMonomial_eq_prefix a u N hu, sequenceMonomial_eq_prefix a v N hv]
  apply hs N
  intro he
  apply huv
  ext i
  by_cases hi : i < N
  · exact congrFun he ⟨i, hi⟩
  · have hui : i ∉ u.support := fun h => hi (Finset.mem_range.mp (hu h))
    have hvi : i ∉ v.support := fun h => hi (Finset.mem_range.mp (hv h))
    rw [Finsupp.not_mem_support_iff.mp hui, Finsupp.not_mem_support_iff.mp hvi]

theorem separated_restrict {m n : ℕ} (a : Fin m → ℝ) (hn : n ≤ m)
    (hs : Separated a) : Separated (fun i : Fin n => a ⟨i.val, by omega⟩) := by
  classical
  intro u v huv
  let eu : Fin m → ℕ := fun i => if h : i.val < n then u ⟨i.val, h⟩ else 0
  let ev : Fin m → ℕ := fun i => if h : i.val < n then v ⟨i.val, h⟩ else 0
  have hne : eu ≠ ev := by
    intro h
    apply huv
    funext i
    have he := congrFun h (⟨i.val, by omega⟩ : Fin m)
    simpa [eu, ev, i.isLt] using he
  have hmono : ∀ w : Fin n → ℕ,
      monomial a (fun i => if h : i.val < n then w ⟨i.val, h⟩ else 0) =
        monomial (fun i : Fin n => a ⟨i.val, by omega⟩) w := by
    intro w
    unfold monomial
    symm
    apply Finset.prod_bij_ne_one (fun i _ _ => (⟨i.val, by omega⟩ : Fin m))
    · simp
    · intro i _ _ j _ _ he
      exact Fin.ext (congrArg (fun z : Fin m => z.val) he)
    · intro j _ hj
      have hjn : j.val < n := by
        by_cases hh : j.val < n
        · exact hh
        · exact False.elim (hj (by simp only [dif_neg hh, pow_zero]))
      refine ⟨⟨j.val, hjn⟩, Finset.mem_univ _, ?_, rfl⟩
      simpa [hjn] using hj
    · intro i _ _
      simp [i.isLt]
  simpa only [eu, ev, hmono] using hs eu ev hne

theorem exists_sequence_extension (hstep : ExtensionStep) {n : ℕ}
    (a : Fin n → ℝ) (ha : ∀ i, 1 < a i) (hmono : StrictMono a)
    (hsep : Separated a) :
    ∃ b : ℕ → ℝ, StrictMono b ∧ (∀ i, 1 < b i) ∧
      (∀ i : Fin n, b i = a i) ∧ SequenceSeparated b := by
  let p : GoodPrefix n := ⟨a, ha, hmono, hsep⟩
  refine ⟨limitSequence hstep p, limitSequence_strictMono hstep p, ?_, ?_, ?_⟩
  · intro i
    exact (prefixChain hstep p (i + 1)).positive ⟨i, by omega⟩
  · intro i
    exact limitSequence_agrees hstep p 0 i
  · apply sequenceSeparated_of_prefixes
    intro N
    have hs := separated_restrict (prefixChain hstep p N).val (show N ≤ n + N by omega)
      (prefixChain hstep p N).separated
    have he : (fun i : Fin N => limitSequence hstep p i) =
        (fun i : Fin N => (prefixChain hstep p N).val ⟨i.val, by omega⟩) := by
      funext i
      exact limitSequence_agrees hstep p N ⟨i.val, by omega⟩
    rw [he]
    exact hs

end E951
