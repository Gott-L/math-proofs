import E922InfiniteEndpoint

/-!
Independent statement harness for the second conjecture on printed page 3
of Erdos--Hajnal, Kromatikus grafokrol (1967), as identified with E922.

This file belongs to the audit, not to proof commit
b1edf8873a1a01edebbf2a12c56276223e1cbb4b. Its definitions below are written
using finite sets, adjacency and an explicit finite-palette function; they
do not alias the submitted predicates or its chromatic-number definition.
The named bridges depend on the submitted complete theorem and must undergo
their own Lean and axiom checks. Preparation alone is not verification.

Folkman proved the mathematics; finite-color compactness is classical.
Codex wrote this audit under Gott-L's direction. This is same-team semantic
checking, not an external referee, a new theorem or a priority claim.
-/

namespace Erdos922IndependentAudit

universe u

/-- One fixed natural k works for every finite vertex selection. Independence
is expressed directly as absence of adjacent selected pairs, including the
harmless diagonal. The cardinal inequality has no truncated subtraction. -/
def OriginalHypothesis {V : Type u} (G : SimpleGraph V) (k : Nat) : Prop :=
  ∀ S : Finset V, ∃ I : Finset V,
    (∀ x, x ∈ I → x ∈ S) ∧
    (∀ x y, x ∈ I → y ∈ I → G.Adj x y → False) ∧
    S.card ≤ 2 * I.card + k

/-- An actual proper function to a palette of exactly k+2 available colors,
with no finite/countable/locally-finite assumption on the vertex type. -/
def OriginalConclusion {V : Type u} (G : SimpleGraph V) (k : Nat) : Prop :=
  ∃ color : V → Fin (k + 2),
    ∀ x y, G.Adj x y → color x ≠ color y

/-- Explicitly audit both directions of the input interpretation. -/
theorem hypothesis_iff_submitted {V : Type u} (G : SimpleGraph V) (k : Nat) :
    OriginalHypothesis G k ↔ Erdos922Adapter.LargeIndependentFinsets G k := by
  constructor
  · intro h S
    obtain ⟨I, hsub, hind, hcard⟩ := h S
    refine ⟨I, hsub, ?_, hcard⟩
    intro x hx y hy _ hxy
    exact hind x y hx hy hxy
  · intro h S
    obtain ⟨I, hsub, hind, hcard⟩ := h S
    refine ⟨I, hsub, ?_, hcard⟩
    intro x y hx hy hxy
    by_cases heq : x = y
    · subst y
      exact G.loopless x hxy
    · exact hind x hx y hy heq hxy

/-- The submitted endpoint implies the literal original finite-palette
question, with no finite-supplier premise added to this statement. -/
theorem original_question {V : Type u} (G : SimpleGraph V) (k : Nat)
    (h : OriginalHypothesis G k) : OriginalConclusion G k := by
  obtain ⟨color⟩ := Erdos922Adapter.colorable_of_largeIndependentFinsets G k
    ((hypothesis_iff_submitted G k).mp h)
  refine ⟨fun x => color x, ?_⟩
  intro x y hxy
  exact color.valid hxy

end Erdos922IndependentAudit
