import PositiveIdempotent
import TrianglePatterns
import FiniteBridge
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
JSP-000746 / Erdős 895, using additive idempotent ultrafilters.
Known mathematical result, with prior complete finite-certificate proofs.
Gott-L initiated and planned the project; Codex reconstructed this argument,
implemented it and performed internal checks. No first-priority claim.
-/

open Filter

attribute [local instance] Ultrafilter.addSemigroup

namespace GottL746

/-- The positive-integer relation statement, with distinct ordered summands. -/
theorem positive_relation_schur (R : ℕ+ → ℕ+ → Prop)
    (hsymm : Symmetric R)
    (htri : ∀ a b c, R a b → R b c → R a c → False) :
    ∃ a b : ℕ+, a < b ∧ ¬R a b ∧ ¬R a (a+b) ∧ ¬R b (a+b) := by
  obtain ⟨U, hid, hne⟩ := exists_positive_idempotent
  have hall := independent_sums_eventually U hid R htri
  obtain ⟨a, ha⟩ := hall.exists
  obtain ⟨b, hb, hba⟩ := (ha.and (hne a)).exists
  by_cases hab : a < b
  · exact ⟨a, b, hab, hb⟩
  · have hlt : b < a := lt_of_le_of_ne (le_of_not_gt hab) hba
    refine ⟨b, a, hlt, ?_, ?_, ?_⟩
    · exact fun h => hb.1 (hsymm h)
    · simpa only [add_comm b a] using hb.2.2
    · simpa only [add_comm b a] using hb.2.1

/-- Every triangle-free graph on the positive integers contains an independent
Schur triple with positive, distinct summands. -/
theorem positive_schur (G : SimpleGraph ℕ+) (hG : G.CliqueFree 3) :
    ∃ a b : ℕ+, a < b ∧ ¬G.Adj a b ∧ ¬G.Adj a (a+b) ∧ ¬G.Adj b (a+b) := by
  apply positive_relation_schur G.Adj G.symm
  intro a b c hab hbc hac
  exact hG {a,b,c} (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)

/-- The catalogue statement on all integers, with a positive ordered witness. -/
theorem integer_schur (G : SimpleGraph ℤ) (hG : G.CliqueFree 3) :
    ∃ a b : ℤ, 0 < a ∧ a < b ∧ ¬G.Adj a b ∧
      ¬G.Adj a (a+b) ∧ ¬G.Adj b (a+b) := by
  let R : ℕ+ → ℕ+ → Prop := fun a b => G.Adj (a : ℤ) (b : ℤ)
  have hs : Symmetric R := fun _ _ h => G.symm h
  have ht : ∀ a b c, R a b → R b c → R a c → False := by
    intro a b c hab hbc hac
    exact hG {(a : ℤ),(b : ℤ),(c : ℤ)}
      (SimpleGraph.is3Clique_triple_iff.mpr ⟨hab,hac,hbc⟩)
  obtain ⟨a,b,hab,hnab,hnas,hnbs⟩ := positive_relation_schur R hs ht
  refine ⟨(a : ℤ),(b : ℤ),?_,?_,hnab,?_,?_⟩
  · exact_mod_cast a.property
  · exact_mod_cast hab
  · simpa [R] using hnas
  · simpa [R] using hnbs

/-- The complete original eventual finite statement; all bridge hypotheses
are discharged. Labels in Fin n denote the positive integers 1,...,n. -/
theorem erdos_895 :
    ∃ N : ℕ, ∀ n ≥ N, ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 →
      ∃ (a b : Fin n) (hsum : a.val + b.val + 1 < n), a.val < b.val ∧
        ¬G.Adj a b ∧ ¬G.Adj a ⟨a.val + b.val + 1, hsum⟩ ∧
        ¬G.Adj b ⟨a.val + b.val + 1, hsum⟩ :=
  eventual_finite_schur_explicit_of_infinite positive_schur

end GottL746
