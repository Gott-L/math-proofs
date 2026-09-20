/-
Inherited recoloring block, original Erdos922.lean lines 4914--5155.
plby/lean-proofs@8822f7ddef30fadbd92e1c6ab4ed897af356af5e,
src/latest/ErdosProblems/Erdos922.lean, SHA256
0bc22004ecbe76ab3cc3f263c29c76994b39017828ea835d987139fa324b9971.
Informal author: Jon Folkman. Formal authors: Codex; GPT-5.6 Sol.
Local Lean 4.19 compatibility work under Gott-L's direction by Codex/A.
Private local work; upstream license unverified; no novelty claim.
-/
import E922EvenCycleBridge

open SimpleGraph
open scoped ENat

namespace Erdos922Recolor

universe u
variable {V : Type u}

-- BEGIN ORIGINAL RECOLOR BLOCK
/-- Recolor an independent set with one fresh color.  The tentative coloring
only has to be proper away from the recolored set, and every unrecolored
vertex has to avoid the fresh color. -/
theorem colorable_add_one_of_recolor_set
    (G : SimpleGraph V) (q : ℕ) (base : V → Fin (q + 1)) (R : Set V)
    (hR : G.IsIndepSet R)
    (hbase : ∀ {v w : V}, G.Adj v w → v ∉ R → w ∉ R → base v ≠ base w)
    (hfresh : ∀ v : V, v ∉ R → base v ≠ Fin.last q) :
    G.Colorable (q + 1) := by
  classical
  refine ⟨SimpleGraph.Coloring.mk
    (fun v ↦ if v ∈ R then Fin.last q else base v) ?_⟩
  intro v w hvw
  by_cases hv : v ∈ R
  · by_cases hw : w ∈ R
    · exact (hR hv hw hvw.ne hvw).elim
    · simp only [if_pos hv, if_neg hw]
      exact (hfresh w hw).symm
  · by_cases hw : w ∈ R
    · simp only [if_neg hv, if_pos hw]
      exact hfresh v hv
    · simp only [if_neg hv, if_neg hw]
      exact hbase hvw hv hw

/-- The set of old vertices which conflict with a proposed coloring of a
distinguished core. -/
def conflictSet (G : SimpleGraph V) (S : Set V)
    (coreColor : S → Fin (q + 1))
    (outsideColor : (G.induce Sᶜ).Coloring (Fin q)) : Set V :=
  {x | ∃ hx : x ∈ Sᶜ, ∃ s : S, G.Adj s.1 x ∧
    coreColor s = Fin.castSucc (outsideColor ⟨x, hx⟩)}

/-- Vertices which receive the fresh color in the standard core recoloring:
the fresh-colored vertices of the core, together with all old vertices whose
old color conflicts with an adjacent core vertex. -/
def freshSet (G : SimpleGraph V) (S : Set V)
    (coreColor : S → Fin (q + 1))
    (outsideColor : (G.induce Sᶜ).Coloring (Fin q)) : Set V :=
  {v | ∃ h : v ∈ S, coreColor ⟨v, h⟩ = Fin.last q} ∪
    conflictSet G S coreColor outsideColor

/-- The structural fact used in both final applications.  Outside vertices
attached to different core vertices are anticomplete, and an outside vertex
attached to one core vertex has no other core neighbor.  These two separation
properties make the automatically defined fresh set independent. -/
theorem freshSet_independent_of_separated_attachments
    (G : SimpleGraph V) (q : ℕ) (S : Set V)
    (coreColor : (G.induce S).Coloring (Fin (q + 1)))
    (outsideColor : (G.induce Sᶜ).Coloring (Fin q))
    (hunique : ∀ {r s : S}, r ≠ s → ∀ {x : V}, x ∉ S →
      G.Adj s.1 x → ¬ G.Adj r.1 x)
    (hanti : ∀ {r s : S}, r ≠ s → ∀ {x y : V}, x ∉ S → y ∉ S →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y) :
    G.IsIndepSet (freshSet G S coreColor outsideColor) := by
  classical
  intro v hv w hw hvw hadj
  change
    (∃ hvS : v ∈ S, coreColor ⟨v, hvS⟩ = Fin.last q) ∨
      ∃ hvO : v ∈ Sᶜ, ∃ s : S, G.Adj s.1 v ∧
        coreColor s = Fin.castSucc (outsideColor ⟨v, hvO⟩) at hv
  change
    (∃ hwS : w ∈ S, coreColor ⟨w, hwS⟩ = Fin.last q) ∨
      ∃ hwO : w ∈ Sᶜ, ∃ s : S, G.Adj s.1 w ∧
        coreColor s = Fin.castSucc (outsideColor ⟨w, hwO⟩) at hw
  rcases hv with ⟨hvS, hvc⟩ | ⟨hvO, s, hsv, hsc⟩
  · rcases hw with ⟨hwS, hwc⟩ | ⟨hwO, s, hsw, hsc⟩
    · exact coreColor.valid
        (show (G.induce S).Adj ⟨v, hvS⟩ ⟨w, hwS⟩ from hadj)
        (hvc.trans hwc.symm)
    · let r : S := ⟨v, hvS⟩
      by_cases hrs : r = s
      · subst s
        exact Fin.castSucc_ne_last (outsideColor ⟨w, hwO⟩) (hsc.symm.trans hvc)
      · exact hunique hrs (by simpa using hwO) hsw hadj
  · rcases hw with ⟨hwS, hwc⟩ | ⟨hwO, t, htw, htc⟩
    · let r : S := ⟨w, hwS⟩
      by_cases hrs : r = s
      · subst s
        exact Fin.castSucc_ne_last (outsideColor ⟨v, hvO⟩) (hsc.symm.trans hwc)
      · exact hunique hrs (by simpa using hvO) hsv hadj.symm
    · by_cases hst : s = t
      · subst t
        apply outsideColor.valid
          (show (G.induce Sᶜ).Adj ⟨v, hvO⟩ ⟨w, hwO⟩ from hadj)
        apply Fin.castSucc_injective q
        exact hsc.symm.trans htc
      · exact hanti hst (by simpa using hvO) (by simpa using hwO) hsv htw hadj

/-- The reusable one-fresh-color extension lemma.  In applications `S` is a
maximum clique or a shortest odd cycle.  All graph-specific work is isolated
in proving that `freshSet` is independent. -/
theorem colorable_of_core_and_independent_conflicts
    (G : SimpleGraph V) (q : ℕ) (S : Set V)
    (coreColor : (G.induce S).Coloring (Fin (q + 1)))
    (outsideColor : (G.induce Sᶜ).Coloring (Fin q))
    (hfresh : G.IsIndepSet (freshSet G S coreColor outsideColor)) :
    G.Colorable (q + 1) := by
  classical
  let base : V → Fin (q + 1) := fun v ↦
    if hv : v ∈ S then coreColor ⟨v, hv⟩
    else Fin.castSucc (outsideColor ⟨v, hv⟩)
  apply colorable_add_one_of_recolor_set G q base
    (freshSet G S coreColor outsideColor) hfresh
  · intro v w hvw hv hw
    by_cases hvS : v ∈ S
    · by_cases hwS : w ∈ S
      · simpa only [base, dif_pos hvS, dif_pos hwS] using
          coreColor.valid (show (G.induce S).Adj ⟨v, hvS⟩ ⟨w, hwS⟩ from hvw)
      · simp only [base, dif_pos hvS, dif_neg hwS]
        intro heq
        apply hw
        right
        exact ⟨hwS, ⟨v, hvS⟩, hvw, heq⟩
    · by_cases hwS : w ∈ S
      · simp only [base, dif_neg hvS, dif_pos hwS]
        intro heq
        apply hv
        right
        exact ⟨hvS, ⟨w, hwS⟩, hvw.symm, heq.symm⟩
      · simp only [base, dif_neg hvS, dif_neg hwS]
        intro heq
        exact outsideColor.valid
          (show (G.induce Sᶜ).Adj ⟨v, hvS⟩ ⟨w, hwS⟩ from hvw)
          (Fin.castSucc_injective _ heq)
  · intro v hv
    by_cases hvS : v ∈ S
    · simp only [base, dif_pos hvS]
      intro heq
      apply hv
      left
      exact ⟨hvS, heq⟩
    · simp only [base, dif_neg hvS]
      exact Fin.castSucc_ne_last _

/-- Prototype of the maximum-clique final recoloring.  The clique hypothesis
is retained to match that application; a proper injective palette on the
clique and independence of the resulting conflict set are the exact facts
needed by the recoloring itself. -/
theorem maximumClique_final_recoloring
    (G : SimpleGraph V) (q : ℕ) (K : Set V)
    (_hK : G.IsClique K)
    (cliqueColor : (G.induce K).Coloring (Fin (q + 1)))
    (outsideColor : (G.induce Kᶜ).Coloring (Fin q))
    (hstruct : G.IsIndepSet (freshSet G K cliqueColor outsideColor)) :
    G.Colorable (q + 1) :=
  colorable_of_core_and_independent_conflicts G q K cliqueColor outsideColor hstruct

/-- Maximum-clique recoloring directly from the two structural neighborhood
properties proved in the mathematical argument. -/
theorem maximumClique_final_recoloring_of_separated_attachments
    (G : SimpleGraph V) (q : ℕ) (K : Set V)
    (_hK : G.IsClique K)
    (cliqueColor : (G.induce K).Coloring (Fin (q + 1)))
    (outsideColor : (G.induce Kᶜ).Coloring (Fin q))
    (hunique : ∀ {r s : K}, r ≠ s → ∀ {x : V}, x ∉ K →
      G.Adj s.1 x → ¬ G.Adj r.1 x)
    (hanti : ∀ {r s : K}, r ≠ s → ∀ {x y : V}, x ∉ K → y ∉ K →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y) :
    G.Colorable (q + 1) :=
  colorable_of_core_and_independent_conflicts G q K cliqueColor outsideColor
    (freshSet_independent_of_separated_attachments G q K cliqueColor outsideColor
      hunique hanti)

/-- Give a finite core pairwise distinct colors whenever it fits in the
target palette.  This is the coloring used on a maximum clique. -/
noncomputable def injectiveCoreColor
    (G : SimpleGraph V) (q : ℕ) (K : Finset V) (hcard : K.card ≤ q + 1) :
    (G.induce (↑K : Set V)).Coloring (Fin (q + 1)) := by
  let e : (↑K : Set V) ↪ Fin (q + 1) := Classical.choice
    (Function.Embedding.nonempty_of_card_le (by simpa using hcard))
  exact SimpleGraph.Coloring.mk e fun {v w} hadj heq ↦
    hadj.ne (e.injective heq)

/-- Fully packaged maximum-clique prototype: the clique's cardinality bound
constructs its injective palette, and the two neighborhood-separation facts
then feed the common fresh-color lemma. -/
theorem maximumClique_final_recoloring_of_card_le
    (G : SimpleGraph V) (q : ℕ) (K : Finset V)
    (_hK : G.IsClique (↑K : Set V)) (hcard : K.card ≤ q + 1)
    (outsideColor : (G.induce ((↑K : Set V)ᶜ)).Coloring (Fin q))
    (hunique : ∀ {r s : (↑K : Set V)}, r ≠ s → ∀ {x : V}, x ∉ K →
      G.Adj s.1 x → ¬ G.Adj r.1 x)
    (hanti : ∀ {r s : (↑K : Set V)}, r ≠ s → ∀ {x y : V}, x ∉ K → y ∉ K →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y) :
    G.Colorable (q + 1) :=
  maximumClique_final_recoloring_of_separated_attachments G q (↑K : Set V) _hK
    (injectiveCoreColor G q K hcard) outsideColor
    hunique hanti

/-- Prototype of the shortest-cycle final recoloring.  Here `C` is the
shortest-cycle vertex set and `cycleColor` is its displayed three-coloring,
embedded in the target palette.  Chordlessness, unique attachment, and
anticompleteness of attachment sets are used upstream precisely to prove
`hstruct`. -/
theorem shortestCycle_final_recoloring
    (G : SimpleGraph V) (q : ℕ) (C : Set V)
    (cycleColor : (G.induce C).Coloring (Fin (q + 1)))
    (outsideColor : (G.induce Cᶜ).Coloring (Fin q))
    (hstruct : G.IsIndepSet (freshSet G C cycleColor outsideColor)) :
    G.Colorable (q + 1) :=
  colorable_of_core_and_independent_conflicts G q C cycleColor outsideColor hstruct

/-- Shortest-cycle recoloring directly from unique attachment to the cycle
and anticompleteness of different attachment sets. -/
theorem shortestCycle_final_recoloring_of_separated_attachments
    (G : SimpleGraph V) (q : ℕ) (C : Set V)
    (cycleColor : (G.induce C).Coloring (Fin (q + 1)))
    (outsideColor : (G.induce Cᶜ).Coloring (Fin q))
    (hunique : ∀ {r s : C}, r ≠ s → ∀ {x : V}, x ∉ C →
      G.Adj s.1 x → ¬ G.Adj r.1 x)
    (hanti : ∀ {r s : C}, r ≠ s → ∀ {x y : V}, x ∉ C → y ∉ C →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y) :
    G.Colorable (q + 1) :=
  colorable_of_core_and_independent_conflicts G q C cycleColor outsideColor
    (freshSet_independent_of_separated_attachments G q C cycleColor outsideColor
      hunique hanti)

/-- Pull the standard tricoloring of a cycle across a graph isomorphism and
embed its three colors in the target palette. -/
noncomputable def cycleCoreColor
    (G : SimpleGraph V) (q n : ℕ) (C : Set V) (hn : 2 ≤ n) (hq : 2 ≤ q)
    (e : G.induce C ≃g SimpleGraph.cycleGraph n) :
    (G.induce C).Coloring (Fin (q + 1)) :=
  (G.induce C).recolorOfCardLE (by simp; omega)
    ((SimpleGraph.cycleGraph.tricoloring n hn).comp e.toHom)

/-- Fully packaged shortest-cycle prototype.  An isomorphism identifies the
induced core with a cycle; the standard three-coloring and the two attachment
separation facts yield the final coloring. -/
theorem shortestCycle_final_recoloring_of_iso
    (G : SimpleGraph V) (q n : ℕ) (C : Set V) (hn : 2 ≤ n) (hq : 2 ≤ q)
    (e : G.induce C ≃g SimpleGraph.cycleGraph n)
    (outsideColor : (G.induce Cᶜ).Coloring (Fin q))
    (hunique : ∀ {r s : C}, r ≠ s → ∀ {x : V}, x ∉ C →
      G.Adj s.1 x → ¬ G.Adj r.1 x)
    (hanti : ∀ {r s : C}, r ≠ s → ∀ {x y : V}, x ∉ C → y ∉ C →
      G.Adj r.1 x → G.Adj s.1 y → ¬ G.Adj x y) :
    G.Colorable (q + 1) :=
  shortestCycle_final_recoloring_of_separated_attachments G q C
    (cycleCoreColor G q n C hn hq e) outsideColor hunique hanti

end Erdos922Recolor
