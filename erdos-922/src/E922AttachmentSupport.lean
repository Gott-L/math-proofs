/- Local compatibility lemma for the Lean4.19 walk decomposition.
   Codex/B under Gott-L's direction. This is a helper to the inherited
   Jon Folkman / plby Codex, GPT-5.6 Sol E922 proof, not a new result claim. -/
import E922AttachmentsCore

open SimpleGraph
namespace Erdos922Recolor
universe u
variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]

theorem support_dropUntil_eq_drop_idxOf {a b x : V} (p : G.Walk a b)
    (hx : x ∈ p.support) :
    (p.dropUntil x hx).support = p.support.drop (p.support.idxOf x) := by
  induction p with
  | nil =>
      have heq := Walk.mem_support_nil_iff.mp hx
      subst x
      simp [Walk.dropUntil]
  | @cons a b c hab p ih =>
      by_cases heq : a = x
      · subst x
        simp [Walk.dropUntil]
      · have hxp : x ∈ p.support := by
          simpa only [Walk.support_cons, List.mem_cons, Ne.symm heq, false_or] using hx
        simp only [Walk.dropUntil, dif_neg heq, Walk.support_cons,
          List.idxOf_cons_ne _ heq, List.drop_succ_cons]
        exact ih hxp

end Erdos922Recolor
