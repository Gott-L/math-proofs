import EGPMatching

/-!
The finite edge-partition extension in the Erdős–Goodman–Pósa induction.
Mathematical argument: Erdős, Goodman and Pósa (1966), Theorem 4.
Project initiation, conception, planning and research direction: Gott-L.
Research, formal implementation and internal checks: Codex assistance, 2026.
Released under the Apache License, Version 2.0.
-/

namespace EGP

variable {V : Type*} [DecidableEq V]

noncomputable def extensionParts (S : Finset V) (R : V → V → Prop)
    (v : V) (M Q : Finset (Finset V)) : Finset (Finset V) :=
  Q ∪ M.image (insert v) ∪
    ((neighbors S R v) \ covered M).image (fun u => ({v, u} : Finset V))

private theorem mem_extensionParts {S : Finset V} {R : V → V → Prop}
    {v : V} {M Q : Finset (Finset V)} {p : Finset V} :
    p ∈ extensionParts S R v M Q ↔
      p ∈ Q ∨ (∃ e ∈ M, insert v e = p) ∨
        ∃ u ∈ neighbors S R v \ covered M, ({v, u} : Finset V) = p := by
  classical
  simp only [extensionParts, Finset.mem_union, Finset.mem_image, or_assoc]

private theorem mem_covered {M : Finset (Finset V)} {a : V} :
    a ∈ covered M ↔ ∃ e ∈ M, a ∈ e := by
  simp [covered]

omit [DecidableEq V] in
private theorem matching_eq_of_common {R : V → V → Prop} {N : Finset V}
    {M : Finset (Finset V)} (hm : MatchingOn R N M)
    {e f : Finset V} (he : e ∈ M) (hf : f ∈ M)
    {a : V} (hae : a ∈ e) (haf : a ∈ f) : e = f := by
  by_contra hne
  exact Finset.disjoint_left.mp (hm.2 he hf hne) hae haf

omit [DecidableEq V] in
private theorem triangle_mem {S : Finset V} {R : V → V → Prop}
    {v : V} {M : Finset (Finset V)} (hi : Irreflexive R)
    (hm : MatchingOn R (neighbors S R v) M) {e : Finset V} (he : e ∈ M) :
    v ∉ e := by
  classical
  intro hv
  have hvn := (hm.1 e he).2.1 hv
  exact hi v ((Finset.mem_filter.mp hvn).2)

theorem extension_partition {S : Finset V} {R : V → V → Prop}
    {v : V} {M Q : Finset (Finset V)}
    (hs : Symmetric R) (hi : Irreflexive R) (hv : v ∈ S)
    (hm : MatchingOn R (neighbors S R v) M)
    (hQ : PartitionOn (S.erase v) (trim R M) Q) :
    PartitionOn S R (extensionParts S R v M Q) := by
  classical
  have hn : ∀ u ∈ neighbors S R v, u ∈ S ∧ R v u := by
    intro u hu
    exact Finset.mem_filter.mp hu
  have hne : ∀ u ∈ neighbors S R v, u ≠ v := by
    intro u hu huv
    exact hi v (huv ▸ (hn u hu).2)
  have hmemQ : ∀ p ∈ Q, ∀ a ∈ p, a ∈ S ∧ a ≠ v := by
    intro p hp a ha
    have h := Finset.mem_erase.mp ((hQ.1 p hp).1 ha)
    exact ⟨h.2, h.1⟩
  have hcover : ∀ a ∈ S, ∀ b ∈ S, R a b →
      ∃ p ∈ extensionParts S R v M Q, a ∈ p ∧ b ∈ p := by
    intro a ha b hb hab
    have hstar : ∀ u ∈ neighbors S R v,
        ∃ p ∈ extensionParts S R v M Q, v ∈ p ∧ u ∈ p := by
      intro u hu
      by_cases hc : u ∈ covered M
      · obtain ⟨e, he, hue⟩ := mem_covered.mp hc
        exact ⟨insert v e, mem_extensionParts.mpr (Or.inr (Or.inl ⟨e, he, rfl⟩)),
          Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hue⟩
      · exact ⟨{v, u}, mem_extensionParts.mpr
          (Or.inr (Or.inr ⟨u, Finset.mem_sdiff.mpr ⟨hu, hc⟩, rfl⟩)),
          Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
    by_cases hav : a = v
    · subst a
      exact hstar b (Finset.mem_filter.mpr ⟨hb, hab⟩)
    by_cases hbv : b = v
    · subst b
      obtain ⟨p, hp, hvp, hap⟩ := hstar a (Finset.mem_filter.mpr ⟨ha, hs hab⟩)
      exact ⟨p, hp, hap, hvp⟩
    by_cases hmab : ∃ e ∈ M, a ∈ e ∧ b ∈ e
    · obtain ⟨e, he, hae, hbe⟩ := hmab
      exact ⟨insert v e, mem_extensionParts.mpr (Or.inr (Or.inl ⟨e, he, rfl⟩)),
        Finset.mem_insert_of_mem hae, Finset.mem_insert_of_mem hbe⟩
    · obtain ⟨p, ⟨hp, hap, hbp⟩, _⟩ :=
        hQ.2 a (Finset.mem_erase.mpr ⟨hav, ha⟩) b
          (Finset.mem_erase.mpr ⟨hbv, hb⟩) ⟨hab, hmab⟩
      exact ⟨p, mem_extensionParts.mpr (Or.inl hp), hap, hbp⟩
  constructor
  · intro p hp
    rcases mem_extensionParts.mp hp with hp | ⟨e, he, rfl⟩ | ⟨u, hu, rfl⟩
    · refine ⟨(hQ.1 p hp).1.trans (Finset.erase_subset _ _), (hQ.1 p hp).2.1, ?_⟩
      intro a ha b hb hab
      exact ((hQ.1 p hp).2.2 a ha b hb hab).1
    · have hve := triangle_mem hi hm he
      refine ⟨Finset.insert_subset_iff.mpr ⟨hv, ?_⟩, Or.inr ?_, ?_⟩
      · exact (hm.1 e he).2.1.trans (Finset.filter_subset _ _)
      · rw [Finset.card_insert_of_not_mem hve, (hm.1 e he).1]
      · intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with hav | hae
        · subst a
          rcases Finset.mem_insert.mp hb with hbv | hbe
          · subst b
            exact (hab rfl).elim
          · exact (hn b ((hm.1 e he).2.1 hbe)).2
        · rcases Finset.mem_insert.mp hb with hbv | hbe
          · subst b
            exact hs ((hn a ((hm.1 e he).2.1 hae)).2)
          · exact (hm.1 e he).2.2 a hae b hbe hab
    · have hun := (Finset.mem_sdiff.mp hu).1
      have hvu : v ≠ u := (hne u hun).symm
      refine ⟨?_, Or.inl (Finset.card_pair hvu), ?_⟩
      · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
        exact ⟨hv, (hn u hun).1⟩
      · intro a ha b hb hab
        have hRvu := (hn u hun).2
        have hRuv := hs hRvu
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
        rcases ha with ha | ha <;> rcases hb with hb | hb <;> subst_vars <;>
          first | exact (hab rfl).elim | assumption
  · intro a ha b hb hab
    have habne : a ≠ b := fun h => hi b (h ▸ hab)
    have old_old : ∀ p ∈ Q, a ∈ p → b ∈ p →
        ∀ q ∈ Q, a ∈ q → b ∈ q → p = q := by
      intro p hp hap hbp q hq haq hbq
      have htrim := (hQ.1 p hp).2.2 a hap b hbp habne
      obtain ⟨t, _, ht⟩ := hQ.2 a ((hQ.1 p hp).1 hap) b
        ((hQ.1 p hp).1 hbp) htrim
      exact (ht p ⟨hp, hap, hbp⟩).trans (ht q ⟨hq, haq, hbq⟩).symm
    have old_tri : ∀ p ∈ Q, a ∈ p → b ∈ p →
        ∀ e ∈ M, ¬ (a ∈ insert v e ∧ b ∈ insert v e) := by
      intro p hp hap hbp e he ⟨hae, hbe⟩
      have hav := (hmemQ p hp a hap).2
      have hbv := (hmemQ p hp b hbp).2
      have hae' := (Finset.mem_insert.mp hae).resolve_left hav
      have hbe' := (Finset.mem_insert.mp hbe).resolve_left hbv
      exact ((hQ.1 p hp).2.2 a hap b hbp habne).2 ⟨e, he, hae', hbe'⟩
    have old_single : ∀ p ∈ Q, a ∈ p → b ∈ p →
        ∀ u : V, ¬ (a ∈ ({v, u} : Finset V) ∧ b ∈ ({v, u} : Finset V)) := by
      intro p hp hap hbp u ⟨hau, hbu⟩
      have hav := (hmemQ p hp a hap).2
      have hbv := (hmemQ p hp b hbp).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hau hbu
      exact habne ((hau.resolve_left hav).trans (hbu.resolve_left hbv).symm)
    have tri_tri : ∀ e ∈ M, a ∈ insert v e → b ∈ insert v e →
        ∀ f ∈ M, a ∈ insert v f → b ∈ insert v f → insert v e = insert v f := by
      intro e he hae hbe f hf haf hbf
      apply congrArg (insert v)
      by_cases hav : a = v
      · have hbv : b ≠ v := by intro hbv; exact habne (hav.trans hbv.symm)
        exact matching_eq_of_common hm he hf
          ((Finset.mem_insert.mp hbe).resolve_left hbv)
          ((Finset.mem_insert.mp hbf).resolve_left hbv)
      · exact matching_eq_of_common hm he hf
          ((Finset.mem_insert.mp hae).resolve_left hav)
          ((Finset.mem_insert.mp haf).resolve_left hav)
    have tri_single : ∀ e ∈ M, a ∈ insert v e → b ∈ insert v e →
        ∀ u ∈ neighbors S R v \ covered M,
          ¬ (a ∈ ({v, u} : Finset V) ∧ b ∈ ({v, u} : Finset V)) := by
      intro e he hae hbe u hu ⟨hau, hbu⟩
      have hunc := (Finset.mem_sdiff.mp hu).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hau hbu
      by_cases hav : a = v
      · have hbv : b ≠ v := by intro hbv; exact habne (hav.trans hbv.symm)
        have hbu' := hbu.resolve_left hbv
        apply hunc
        rw [← hbu']
        exact mem_covered.mpr ⟨e, he, (Finset.mem_insert.mp hbe).resolve_left hbv⟩
      · have hau' := hau.resolve_left hav
        apply hunc
        rw [← hau']
        exact mem_covered.mpr ⟨e, he, (Finset.mem_insert.mp hae).resolve_left hav⟩
    have single_single : ∀ u w : V,
        a ∈ ({v, u} : Finset V) → b ∈ ({v, u} : Finset V) →
        a ∈ ({v, w} : Finset V) → b ∈ ({v, w} : Finset V) →
        ({v, u} : Finset V) = {v, w} := by
      intro u w hau hbu haw hbw
      suffices u = w by rw [this]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hau hbu haw hbw
      by_cases hav : a = v
      · have hbv : b ≠ v := by intro hbv; exact habne (hav.trans hbv.symm)
        exact (hbu.resolve_left hbv).symm.trans (hbw.resolve_left hbv)
      · exact (hau.resolve_left hav).symm.trans (haw.resolve_left hav)
    obtain ⟨p, hp, hap, hbp⟩ := hcover a ha b hb hab
    refine ⟨p, ⟨hp, hap, hbp⟩, ?_⟩
    rintro q ⟨hq, haq, hbq⟩
    rcases mem_extensionParts.mp hp with hp | ⟨e, he, rfl⟩ | ⟨u, hu, rfl⟩ <;>
      rcases mem_extensionParts.mp hq with hq | ⟨f, hf, rfl⟩ | ⟨w, hw, rfl⟩
    · exact (old_old p hp hap hbp q hq haq hbq).symm
    · exact (old_tri p hp hap hbp f hf ⟨haq, hbq⟩).elim
    · exact (old_single p hp hap hbp w ⟨haq, hbq⟩).elim
    · exact (old_tri q hq haq hbq e he ⟨hap, hbp⟩).elim
    · exact (tri_tri e he hap hbp f hf haq hbq).symm
    · exact (tri_single e he hap hbp w hw ⟨haq, hbq⟩).elim
    · exact (old_single q hq haq hbq u ⟨hap, hbp⟩).elim
    · exact (tri_single f hf haq hbq u hu ⟨hap, hbp⟩).elim
    · exact (single_single u w hap hbp haq hbq).symm

theorem extension_card_le {S : Finset V} {R : V → V → Prop}
    {v : V} {M Q : Finset (Finset V)}
    (hm : MatchingOn R (neighbors S R v) M) :
    (extensionParts S R v M Q).card ≤
      Q.card + ((neighbors S R v).card - M.card) := by
  classical
  have hc := matching_covered_subset hm
  have hcc := matching_covered_card hm
  have hcN := Finset.card_le_card hc
  rw [hcc] at hcN
  have h₁ := Finset.card_union_le Q (M.image (insert v))
  have h₂ := Finset.card_image_le (s := M) (f := insert v)
  have h₃ := Finset.card_image_le
    (s := neighbors S R v \ covered M) (f := fun u => ({v, u} : Finset V))
  rw [Finset.card_sdiff hc, hcc] at h₃
  have h₄ := Finset.card_union_le (Q ∪ M.image (insert v))
    ((neighbors S R v \ covered M).image (fun u => ({v, u} : Finset V)))
  change (extensionParts S R v M Q).card ≤ _ at h₄
  omega

/-- Reinsert the center using one triangle per matching edge and one edge per
unmatched neighbor. Every original edge has exactly one owner. -/
theorem extend_partition (S : Finset V) (R : V → V → Prop)
    (v : V) (M Q : Finset (Finset V))
    (hs : Symmetric R) (hi : Irreflexive R) (hv : v ∈ S)
    (hm : MatchingOn R (neighbors S R v) M)
    (hQ : PartitionOn (S.erase v) (trim R M) Q) :
    ∃ P, PartitionOn S R P ∧
      P.card ≤ Q.card + ((neighbors S R v).card - M.card) :=
  ⟨extensionParts S R v M Q, extension_partition hs hi hv hm hQ,
    extension_card_le hm⟩

end EGP
