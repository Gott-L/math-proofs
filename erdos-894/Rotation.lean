import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
An independently written implementation of the standard nested-middle-half
interval argument for lacunary sequences. This mathematical argument predates
this project (see the introduction of Peres--Schlag, 2010). Prior Lean work was
known when this implementation was commissioned; no first-formalization or
independent-discovery claim is made, and no problem-specific Lean was copied.
-/

namespace GottL894

/-- Choose a middle-half interval at the finer scale inside the given interval. -/
private lemma next_interval (p q a : ℝ) (hp : 0 < p) (hgap : 4 * p ≤ q) :
    let z : ℤ := ⌈q * a - 1 / 4⌉
    a ≤ ((z : ℝ) + 1 / 4) / q ∧
      ((z : ℝ) + 3 / 4) / q ≤ a + (1 / 2) / p := by
  dsimp only
  have hq : 0 < q := by linarith
  have hlo := Int.le_ceil (q * a - 1 / 4)
  have hhi := Int.ceil_lt_add_one (q * a - 1 / 4)
  constructor
  · apply (le_div_iff₀ hq).2
    nlinarith
  · have hfirst :
        ((⌈q * a - 1 / 4⌉ : ℤ) : ℝ) + 3 / 4 <
          (a + (3 / 2) / q) * q := by
      rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hq)]
      nlinarith
    have hsecond : (3 / 2 : ℝ) / q ≤ (1 / 2) / p := by
      apply (div_le_div_iff₀ hq hp).2
      nlinarith
    exact (div_lt_iff₀ hq).2 hfirst |>.le.trans (add_le_add_left hsecond a)

private noncomputable def intervalLabel (m : ℕ → ℕ) : ℕ → ℤ
  | 0 => 0
  | k + 1 =>
      ⌈(m (k + 1) : ℝ) * (((intervalLabel m k : ℤ) : ℝ) + 1 / 4) /
        (m k : ℝ) - 1 / 4⌉

private noncomputable def lower (m : ℕ → ℕ) (k : ℕ) : ℝ :=
  ((intervalLabel m k : ℝ) + 1 / 4) / (m k : ℝ)

private noncomputable def upper (m : ℕ → ℕ) (k : ℕ) : ℝ :=
  ((intervalLabel m k : ℝ) + 3 / 4) / (m k : ℝ)

private lemma upper_eq (m : ℕ → ℕ) (k : ℕ) :
    upper m k = lower m k + (1 / 2 : ℝ) / (m k : ℝ) := by
  unfold upper lower
  ring

private lemma nested_step (m : ℕ → ℕ) (hpos : ∀ k, 0 < m k)
    (hgap : ∀ k, 4 * m k ≤ m (k + 1)) (k : ℕ) :
    lower m k ≤ lower m (k + 1) ∧ upper m (k + 1) ≤ upper m k := by
  have hp : (0 : ℝ) < m k := by exact_mod_cast hpos k
  have hg : (4 : ℝ) * m k ≤ m (k + 1) := by exact_mod_cast hgap k
  have h := next_interval (m k : ℝ) (m (k + 1) : ℝ) (lower m k) hp hg
  rw [upper_eq m k]
  simpa only [lower, upper, intervalLabel, mul_div_assoc] using h

/-- A positive sequence with successive ratio at least four admits one rotation
whose sampled values all belong to integer translates of the closed middle half. -/
theorem exists_rotation (m : ℕ → ℕ) (hpos : ∀ k, 0 < m k)
    (hgap : ∀ k, 4 * m k ≤ m (k + 1)) :
    ∃ θ : ℝ, ∀ k, ∃ z : ℤ,
      (z : ℝ) + 1 / 4 ≤ θ * (m k : ℝ) ∧
        θ * (m k : ℝ) ≤ (z : ℝ) + 3 / 4 := by
  have hlow : Monotone (lower m) :=
    monotone_nat_of_le_succ fun k => (nested_step m hpos hgap k).1
  have hupp : Antitone (upper m) :=
    antitone_nat_of_succ_le fun k => (nested_step m hpos hgap k).2
  have hlu : ∀ k, lower m k ≤ upper m k := by
    intro k
    rw [upper_eq]
    have hp : (0 : ℝ) < m k := by exact_mod_cast hpos k
    have : (0 : ℝ) ≤ (1 / 2 : ℝ) / (m k : ℝ) :=
      div_nonneg (by norm_num) hp.le
    linarith
  have all_le : ∀ j k, lower m j ≤ upper m k := by
    intro j k
    rcases le_total j k with hjk | hkj
    · exact (hlow hjk).trans (hlu k)
    · exact (hlu j).trans (hupp hkj)
  have hbdd : BddAbove (Set.range (lower m)) := by
    refine ⟨upper m 0, ?_⟩
    rintro _ ⟨j, rfl⟩
    exact all_le j 0
  have hnonempty : (Set.range (lower m)).Nonempty := ⟨lower m 0, 0, rfl⟩
  refine ⟨sSup (Set.range (lower m)), ?_⟩
  intro k
  have hleft : lower m k ≤ sSup (Set.range (lower m)) :=
    le_csSup hbdd ⟨k, rfl⟩
  have hright : sSup (Set.range (lower m)) ≤ upper m k := by
    apply csSup_le hnonempty
    rintro _ ⟨j, rfl⟩
    exact all_le j k
  have hp : (0 : ℝ) < m k := by exact_mod_cast hpos k
  exact ⟨intervalLabel m k, (div_le_iff₀ hp).1 hleft,
    (le_div_iff₀ hp).1 hright⟩

end GottL894
