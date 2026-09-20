import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.Push

/-!
Compactness from the positive-integer graph statement to the original eventual
finite statement. Fin n labels i represent the positive integer i+1, so the
label of a sum is a.val+b.val+1. No explicit threshold (such as 18) is claimed.
The infinite theorem is a parameter here and is discharged by the final module.
-/

open Filter

namespace GottL746

/-- Extend a finite graph to positive integers, with all out-of-range points isolated. -/
def boundedPullback {n : ℕ} (G : SimpleGraph (Fin n)) : SimpleGraph ℕ+ where
  Adj a b := ∃ (ha : a.natPred < n) (hb : b.natPred < n),
    G.Adj ⟨a.natPred, ha⟩ ⟨b.natPred, hb⟩
  symm := by
    rintro a b ⟨ha, hb, hab⟩
    exact ⟨hb, ha, G.symm hab⟩
  loopless := by
    rintro a ⟨ha, hb, haa⟩
    exact G.loopless ⟨a.natPred, ha⟩ haa

theorem boundedPullback_cliqueFree {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : G.CliqueFree 3) : (boundedPullback G).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp hs
  obtain ⟨ha, hb, hab⟩ := hab
  obtain ⟨_, hc, hac⟩ := hac
  obtain ⟨_, _, hbc⟩ := hbc
  exact hG {⟨a.natPred, ha⟩, ⟨b.natPred, hb⟩, ⟨c.natPred, hc⟩}
    (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab, hac, hbc⟩)

/-- The pointwise ultrafilter limit of adjacency is an actual simple graph. -/
def ultrafilterGraph {I V : Type*} (U : Ultrafilter I)
    (G : I → SimpleGraph V) : SimpleGraph V where
  Adj a b := ∀ᶠ i in U, (G i).Adj a b
  symm := by
    intro a b h
    exact h.mono fun i hi => (G i).symm hi
  loopless := by
    intro a h
    obtain ⟨i, hi⟩ := h.exists
    exact (G i).loopless a hi

theorem ultrafilterGraph_cliqueFree {I V : Type*} (U : Ultrafilter I)
    (G : I → SimpleGraph V) (hG : ∀ i, (G i).CliqueFree 3) :
    (ultrafilterGraph U G).CliqueFree 3 := by
  classical
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, _⟩ := SimpleGraph.is3Clique_iff.mp hs
  obtain ⟨i, habi, haci, hbci⟩ := (hab.and (hac.and hbc)).exists
  exact hG i {a, b, c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨habi, haci, hbci⟩)

/-- The finite labelled version uses positive values one greater than the labels. -/
def FiniteSchur (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (a b : Fin n) (hsum : a.val + b.val + 1 < n),
    a.val < b.val ∧ ¬G.Adj a b ∧
      ¬G.Adj a ⟨a.val + b.val + 1, hsum⟩ ∧
      ¬G.Adj b ⟨a.val + b.val + 1, hsum⟩

theorem finiteSchur_of_boundedPullback {n : ℕ} (G : SimpleGraph (Fin n))
    (a b : ℕ+) (hab : a < b) (hsum : (a + b).natPred < n)
    (h₁ : ¬(boundedPullback G).Adj a b)
    (h₂ : ¬(boundedPullback G).Adj a (a + b))
    (h₃ : ¬(boundedPullback G).Adj b (a + b)) : FiniteSchur n G := by
  have heq : (a + b).natPred = a.natPred + b.natPred + 1 := by
    have ha := a.natPred_add_one
    have hb := b.natPred_add_one
    have hs := (a + b).natPred_add_one
    rw [PNat.add_coe] at hs
    omega
  have ha : a.natPred < n := by omega
  have hb : b.natPred < n := by omega
  have hsum' : a.natPred + b.natPred + 1 < n := by omega
  refine ⟨⟨a.natPred, ha⟩, ⟨b.natPred, hb⟩, hsum', ?_, ?_, ?_, ?_⟩
  · exact PNat.natPred_strictMono hab
  · intro h
    exact h₁ ⟨ha, hb, h⟩
  · intro h
    apply h₂
    refine ⟨ha, hsum, ?_⟩
    simpa only [heq] using h
  · intro h
    apply h₃
    refine ⟨hb, hsum, ?_⟩
    simpa only [heq] using h

/-- Arbitrarily large finite counterexamples would have an infinite ultrafilter
limit counterexample. This supplies a uniform threshold, not a numeric value. -/
theorem eventual_finite_schur_of_infinite
    (hInfinite : ∀ G : SimpleGraph ℕ+, G.CliqueFree 3 →
      ∃ a b, a < b ∧ ¬G.Adj a b ∧ ¬G.Adj a (a + b) ∧ ¬G.Adj b (a + b)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n),
      G.CliqueFree 3 → FiniteSchur n G := by
  classical
  by_contra hfail
  push_neg at hfail
  choose size hsize graph hfree hbad using hfail
  let U := Filter.hyperfilter ℕ
  let graphs (k : ℕ) := boundedPullback (graph k)
  let limit := ultrafilterGraph U graphs
  have hlimit : limit.CliqueFree 3 :=
    ultrafilterGraph_cliqueFree U graphs (fun k => boundedPullback_cliqueFree _ (hfree k))
  obtain ⟨a, b, hab, h₁, h₂, h₃⟩ := hInfinite limit hlimit
  have h₁' : ∀ᶠ k in U, ¬(graphs k).Adj a b := Ultrafilter.eventually_not.mpr h₁
  have h₂' : ∀ᶠ k in U, ¬(graphs k).Adj a (a + b) := Ultrafilter.eventually_not.mpr h₂
  have h₃' : ∀ᶠ k in U, ¬(graphs k).Adj b (a + b) := Ultrafilter.eventually_not.mpr h₃
  have hbound : ∀ᶠ k in U, (a + b).natPred < size k := by
    have hlarge : ∀ᶠ k in U, (a + b).natPred < k :=
      Nat.hyperfilter_le_atTop (Filter.eventually_gt_atTop _)
    exact hlarge.mono fun k hk => lt_of_lt_of_le hk (hsize k)
  obtain ⟨k, hk, hka, hkb, hkc⟩ := (hbound.and (h₁'.and (h₂'.and h₃'))).exists
  exact hbad k (finiteSchur_of_boundedPullback (graph k) a b hab hk hka hkb hkc)

/-- Fully expanded finite endpoint for direct statement comparison. -/
theorem eventual_finite_schur_explicit_of_infinite
    (hInfinite : ∀ G : SimpleGraph ℕ+, G.CliqueFree 3 →
      ∃ a b, a < b ∧ ¬G.Adj a b ∧ ¬G.Adj a (a + b) ∧ ¬G.Adj b (a + b)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
      ∃ (a b : Fin n) (hsum : a.val + b.val + 1 < n), a.val < b.val ∧
        ¬G.Adj a b ∧ ¬G.Adj a ⟨a.val + b.val + 1, hsum⟩ ∧
        ¬G.Adj b ⟨a.val + b.val + 1, hsum⟩ :=
  eventual_finite_schur_of_infinite hInfinite

end GottL746
