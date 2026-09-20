import Mathlib.Combinatorics.Hindman

/-!
Three adjacency patterns over an additive idempotent ultrafilter.
The order of nested quantifiers is fixed throughout; no commutativity of
ultrafilter addition or exchange of quantifiers is used.
-/

open Filter

namespace GottL746

attribute [local instance] Ultrafilter.addSemigroup

variable {M : Type*} [AddSemigroup M]

/-- Fold the first two variables, preserving the order of all three. -/
theorem eventually_add_first (U : Ultrafilter M) (hid : U + U = U)
    {P : M → M → Prop} (h : ∀ᶠ a in U, ∀ᶠ b in U, P a b) :
    ∀ᶠ a in U, ∀ᶠ b in U, ∀ᶠ c in U, P (a + b) c := by
  exact (Ultrafilter.eventually_add U U (fun x => ∀ᶠ c in U, P x c)).mp
    (by simpa only [hid] using h)

/-- Fold the last two variables while leaving the first one fixed. -/
theorem eventually_add_second (U : Ultrafilter M) (hid : U + U = U)
    {P : M → M → Prop} (h : ∀ᶠ a in U, ∀ᶠ b in U, P a b) :
    ∀ᶠ a in U, ∀ᶠ b in U, ∀ᶠ c in U, P a (b + c) := by
  filter_upwards [h] with a ha
  exact (Ultrafilter.eventually_add U U (fun y => P a y)).mp
    (by simpa only [hid] using ha)

omit [AddSemigroup M] in
/-- An ordered product of ultrafilters also decides a predicate. -/
theorem eventually_pair_not (U : Ultrafilter M) {P : M → M → Prop}
    (h : ¬ (∀ᶠ a in U, ∀ᶠ b in U, P a b)) :
    ∀ᶠ a in U, ∀ᶠ b in U, ¬P a b := by
  have houter : ∀ᶠ a in U, ¬ (∀ᶠ b in U, P a b) :=
    Ultrafilter.eventually_not.mpr h
  exact houter.mono (fun _ ha => Ultrafilter.eventually_not.mpr ha)

omit [AddSemigroup M] in
/-- The direct pattern cannot be large for a triangle-free relation. -/
theorem not_eventually_direct (U : Ultrafilter M) (R : M → M → Prop)
    (htri : ∀ a b c, R a b → R b c → R a c → False) :
    ¬ (∀ᶠ a in U, ∀ᶠ b in U, R a b) := by
  intro h
  obtain ⟨a, ha⟩ := h.exists
  obtain ⟨b, hab, hb⟩ := (ha.and h).exists
  obtain ⟨c, hac, hbc⟩ := (ha.and hb).exists
  exact htri a b c hab hbc hac

/-- A large left-summand pattern creates a triangle on successive sums. -/
theorem not_eventually_left_sum (U : Ultrafilter M) (hid : U + U = U)
    (R : M → M → Prop)
    (htri : ∀ a b c, R a b → R b c → R a c → False) :
    ¬ (∀ᶠ a in U, ∀ᶠ b in U, R a (a + b)) := by
  intro h
  have hl := eventually_add_first U hid h
  have hr := eventually_add_second U hid h
  obtain ⟨a, ha, hla, hra⟩ := (h.and (hl.and hr)).exists
  obtain ⟨b, hab, hlb, hrb⟩ := (ha.and (hla.and hra)).exists
  obtain ⟨c, hbc, hac⟩ := (hlb.and hrb).exists
  exact htri a (a + b) ((a + b) + c) hab hbc
    (by simpa only [add_assoc] using hac)

/-- A large right-summand pattern creates a triangle on reverse partial sums.
The variables still occur in the original order `a`, `b`, `c`. -/
theorem not_eventually_right_sum (U : Ultrafilter M) (hid : U + U = U)
    (R : M → M → Prop)
    (htri : ∀ a b c, R a b → R b c → R a c → False) :
    ¬ (∀ᶠ a in U, ∀ᶠ b in U, R b (a + b)) := by
  intro h
  have hl := eventually_add_first U hid h
  have hr := eventually_add_second U hid h
  obtain ⟨a, hla, hra⟩ := (hl.and hr).exists
  obtain ⟨b, hb, hlb, hrb⟩ := (h.and (hla.and hra)).exists
  obtain ⟨c, hcb, hct, hbt⟩ := (hb.and (hlb.and hrb)).exists
  exact htri c (b + c) ((a + b) + c) hcb
    (by simpa only [add_assoc] using hbt) hct

/-- All three Schur-triple edges are absent on a large ordered set of pairs.
This core needs only associativity and the displayed triangle prohibition.
Distinctness of the summands is supplied separately by nonprincipality. -/
theorem independent_sums_eventually (U : Ultrafilter M) (hid : U + U = U)
    (R : M → M → Prop)
    (htri : ∀ a b c, R a b → R b c → R a c → False) :
    ∀ᶠ a in U, ∀ᶠ b in U,
      ¬R a b ∧ ¬R a (a + b) ∧ ¬R b (a + b) := by
  have hA := eventually_pair_not U (not_eventually_direct U R htri)
  have hB := eventually_pair_not U (not_eventually_left_sum U hid R htri)
  have hC := eventually_pair_not U (not_eventually_right_sum U hid R htri)
  filter_upwards [hA, hB, hC] with a ha hb hc
  filter_upwards [ha, hb, hc] with b hab hal hbr
  exact ⟨hab, hal, hbr⟩

end GottL746
