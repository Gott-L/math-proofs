import Jsp399Witness
import EncodedCoeffCertificate

/-!
A five-integer-parameter identity for all three-element subset sums of
27 indexed linear forms. The coefficient vectors are 0, ±2 times the
five unit vectors, and the 16 sign vectors with an even number of minus
signs. Their negatives give the second family.

The fixed vector-valued identity is checked in Lean's kernel and then
transported to every parameter tuple by linear evaluation. Parameters
may produce repeated values; when both evaluated lists have no repeated
entries, these are ordinary finite-set subset sums with multiplicity.

No mathematical novelty or first-formalization claim is made.
MIT license. Written with OpenAI Codex assistance, 2026-09-17.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JSP399Parametric

open JSP399TwentySeven

abbrev Vec := Int × Int × Int × Int × Int

def coefficientVectors : List Vec :=
  [(0,0,0,0,-2), (1,-1,-1,-1,-1), (-1,1,-1,-1,-1),
   (-1,-1,1,-1,-1), (1,1,1,-1,-1), (-1,-1,-1,1,-1),
   (1,1,-1,1,-1), (0,0,0,-2,0), (1,-1,1,1,-1),
   (-1,1,1,1,-1), (0,0,-2,0,0), (0,-2,0,0,0),
   (-2,0,0,0,0), (0,0,0,0,0), (2,0,0,0,0),
   (0,2,0,0,0), (0,0,2,0,0), (-1,-1,-1,-1,1),
   (1,1,-1,-1,1), (0,0,0,2,0), (1,-1,1,-1,1),
   (-1,1,1,-1,1), (1,-1,-1,1,1), (-1,1,-1,1,1),
   (-1,-1,1,1,1), (1,1,1,1,1), (0,0,0,0,2)]

theorem coefficientVectors_length : coefficientVectors.length = 27 := by decide

theorem coefficientVectors_nodup : coefficientVectors.Nodup := by decide

def vectorA (i : Index) : Vec :=
  coefficientVectors[i.val]'(by simpa only [coefficientVectors_length] using i.isLt)

def vneg (v : Vec) : Vec :=
  (-v.1, -v.2.1, -v.2.2.1, -v.2.2.2.1, -v.2.2.2.2)

def vectorB (i : Index) : Vec := vneg (vectorA i)

def vadd (a b : Vec) : Vec :=
  (a.1+b.1, a.2.1+b.2.1, a.2.2.1+b.2.2.1,
   a.2.2.2.1+b.2.2.2.1, a.2.2.2.2+b.2.2.2.2)

def vectorSums (a : Index → Vec) : List Vec :=
  triples.map (fun p => vadd (vadd (a p.1) (a p.2.1)) (a p.2.2))

def encodeCoeff (v : Vec) : Int :=
  (v.1+6) + 13*((v.2.1+6) + 13*((v.2.2.1+6) +
    13*((v.2.2.2.1+6) + 13*(v.2.2.2.2+6))))

def coeffBounds (v : Vec) : Prop :=
  (-6 ≤ v.1 ∧ v.1 ≤ 6) ∧
  (-6 ≤ v.2.1 ∧ v.2.1 ≤ 6) ∧
  (-6 ≤ v.2.2.1 ∧ v.2.2.1 ≤ 6) ∧
  (-6 ≤ v.2.2.2.1 ∧ v.2.2.2.1 ≤ 6) ∧
  (-6 ≤ v.2.2.2.2 ∧ v.2.2.2.2 ≤ 6)

theorem encodeCoeff_inj (a b : Vec) (ha : coeffBounds a)
    (hb : coeffBounds b) (he : encodeCoeff a = encodeCoeff b) : a = b := by
  rcases a with ⟨a0,a1,a2,a3,a4⟩
  rcases b with ⟨b0,b1,b2,b3,b4⟩
  simp only [encodeCoeff] at he
  simp only [coeffBounds] at ha hb
  have h0 : a0 = b0 := by omega
  have h1 : a1 = b1 := by omega
  have h2 : a2 = b2 := by omega
  have h3 : a3 = b3 := by omega
  have h4 : a4 = b4 := by omega
  simp [h0,h1,h2,h3,h4]


theorem perm_of_map_injOn {α β : Type} (f : α → β) (P : α → Prop)
    (hf : ∀ a b, P a → P b → f a = f b → a = b)
    (xs ys : List α) (hx : ∀ a ∈ xs, P a) (hy : ∀ b ∈ ys, P b)
    (hm : (xs.map f).Perm (ys.map f)) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
      have hn : ys.length = 0 := by simpa using hm.length_eq.symm
      rw [List.eq_nil_of_length_eq_zero hn]
  | cons a xs ih =>
      have hfa : f a ∈ ys.map f := hm.mem_iff.mp (by simp)
      obtain ⟨b, hb, he⟩ := List.mem_map.mp hfa
      have hab : a = b := hf a b (hx a (by simp)) (hy b hb) he.symm
      subst b
      obtain ⟨before, after, rfl⟩ := List.append_of_mem hb
      have hrest : (xs.map f).Perm ((before ++ after).map f) := by
        simp only [List.map_cons, List.map_append] at hm ⊢
        exact (hm.trans List.perm_middle).cons_inv
      have hxr : ∀ x ∈ xs, P x := by
        intro x hxx
        exact hx x (by simp [hxx])
      have hyr : ∀ x ∈ before ++ after, P x := by
        intro x hxx
        apply hy x
        simp only [List.mem_append, List.mem_cons] at hxx ⊢
        rcases hxx with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      exact ((ih (before ++ after) hxr hyr hrest).cons a).trans List.perm_middle.symm



def sourceBounds (v : Vec) : Prop :=
  (-2 ≤ v.1 ∧ v.1 ≤ 2) ∧
  (-2 ≤ v.2.1 ∧ v.2.1 ≤ 2) ∧
  (-2 ≤ v.2.2.1 ∧ v.2.2.1 ≤ 2) ∧
  (-2 ≤ v.2.2.2.1 ∧ v.2.2.2.1 ≤ 2) ∧
  (-2 ≤ v.2.2.2.2 ∧ v.2.2.2.2 ≤ 2)

theorem vectorA_bounds : ∀ i : Index, sourceBounds (vectorA i) := by
  unfold sourceBounds
  decide
theorem vectorB_bounds : ∀ i : Index, sourceBounds (vectorB i) := by
  unfold sourceBounds
  decide

theorem triple_bounds (a b c : Vec) (ha : sourceBounds a)
    (hb : sourceBounds b) (hc : sourceBounds c) :
    coeffBounds (vadd (vadd a b) c) := by
  simp only [sourceBounds] at ha hb hc
  simp only [coeffBounds, vadd]
  omega

theorem vectorSums_bounds (a : Index → Vec)
    (ha : ∀ i, sourceBounds (a i)) :
    ∀ v ∈ vectorSums a, coeffBounds v := by
  intro v hv
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hv
  exact triple_bounds _ _ _ (ha t.1) (ha t.2.1) (ha t.2.2)

def encodeSource (v : Vec) : Int :=
  (v.1+2) + 13*((v.2.1+2) + 13*((v.2.2.1+2) +
    13*((v.2.2.2.1+2) + 13*(v.2.2.2.2+2))))

theorem encode_triple (a b c : Vec) :
    encodeCoeff (vadd (vadd a b) c) =
      encodeSource a + encodeSource b + encodeSource c := by
  simp only [encodeCoeff, encodeSource, vadd]
  omega

theorem codeA_matches : ∀ i : Index,
    (JSP399CoeffCertificate.codeA i : Int) = encodeSource (vectorA i) := by decide

theorem codeB_matches : ∀ i : Index,
    (JSP399CoeffCertificate.codeB i : Int) = encodeSource (vectorB i) := by decide

theorem encoded_sums (a : Index → Vec) (c : Index → Nat)
    (hc : ∀ i, (c i : Int) = encodeSource (a i)) :
    (tripleSums c).map (fun n : Nat => (n : Int)) =
      (vectorSums a).map encodeCoeff := by
  simp only [tripleSums, vectorSums, List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, Int.natCast_add, hc, encode_triple]

/-- The scalar certificate loses no information: base 13 is injective
on all coefficient sums in the verified coordinate bounds. -/
theorem vector_triple_sums_perm : (vectorSums vectorA).Perm (vectorSums vectorB) := by
  have h := JSP399CoeffCertificate.encoded_triple_sums_perm.map (fun n : Nat => (n : Int))
  rw [encoded_sums vectorA _ codeA_matches, encoded_sums vectorB _ codeB_matches] at h
  exact perm_of_map_injOn encodeCoeff coeffBounds encodeCoeff_inj _ _
    (vectorSums_bounds _ vectorA_bounds) (vectorSums_bounds _ vectorB_bounds) h

/-- Any additive interpretation of the five coefficient coordinates
preserves the complete spectrum, including multiplicity. -/
theorem every_additive_image_collision {α : Type} [Add α]
    (f : Vec → α) (hf : ∀ a b, f (vadd a b) = f a + f b) :
    (triples.map (fun t => f (vectorA t.1) + f (vectorA t.2.1) + f (vectorA t.2.2))).Perm
      (triples.map (fun t => f (vectorB t.1) + f (vectorB t.2.1) + f (vectorB t.2.2))) := by
  have h := vector_triple_sums_perm.map f
  simpa only [vectorSums, List.map_map, Function.comp_def, hf] using h

def evaluate (p v : Vec) : Int :=
  p.1*v.1 + p.2.1*v.2.1 + p.2.2.1*v.2.2.1 +
    p.2.2.2.1*v.2.2.2.1 + p.2.2.2.2*v.2.2.2.2

theorem evaluate_add (p a b : Vec) :
    evaluate p (vadd a b) = evaluate p a + evaluate p b := by
  simp only [evaluate, vadd, Int.mul_add]
  omega

theorem evaluate_neg (p v : Vec) : evaluate p (vneg v) = -evaluate p v := by
  simp only [evaluate, vneg, Int.mul_neg]
  omega

def familyA (p : Vec) (i : Index) : Int := evaluate p (vectorA i)
def familyB (p : Vec) (i : Index) : Int := evaluate p (vectorB i)

def integerTripleSums (a : Index → Int) : List Int :=
  triples.map (fun p => a p.1 + a p.2.1 + a p.2.2)

def SameIntegerTripleSums (a b : Index → Int) : Prop :=
  (integerTripleSums a).Perm (integerTripleSums b)

theorem evaluate_vector_sums (p : Vec) (a : Index → Vec) :
    (vectorSums a).map (evaluate p) =
      integerTripleSums (fun i => evaluate p (a i)) := by
  simp only [vectorSums, integerTripleSums, List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp_apply, evaluate_add]

/-- The complete identity holds for every tuple of five integer parameters. -/
theorem every_parameter_collision (p : Vec) :
    SameIntegerTripleSums (familyA p) (familyB p) := by
  have h := vector_triple_sums_perm.map (evaluate p)
  rw [evaluate_vector_sums, evaluate_vector_sums] at h
  exact h

def translated (shift : Int) (a : Index → Int) : Index → Int :=
  fun i => shift + a i

theorem translated_sums (shift : Int) (a : Index → Int) :
    integerTripleSums (translated shift a) =
      (integerTripleSums a).map (fun s => 3*shift+s) := by
  simp only [integerTripleSums, List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [translated, Function.comp_apply]
  omega

/-- A common translation preserves the full parametric collision. -/
theorem every_translated_parameter_collision (shift : Int) (p : Vec) :
    SameIntegerTripleSums (translated shift (familyA p))
      (translated shift (familyB p)) := by
  unfold SameIntegerTripleSums
  rw [translated_sums, translated_sums]
  exact (every_parameter_collision p).map (fun s => 3*shift+s)

def values (a : Index → Int) : List Int := indices.map a

theorem values_length (a : Index → Int) : (values a).length = 27 := by
  simp [values, indices]

/-- The indexed sums represent finite sets whenever the evaluated values
are distinct; the equality itself requires no distinctness assumption. -/
theorem collision_with_distinct_entries (shift : Int) (p : Vec)
    (ha : (values (translated shift (familyA p))).Nodup)
    (hb : (values (translated shift (familyB p))).Nodup) :
    (values (translated shift (familyA p))).length = 27 ∧
    (values (translated shift (familyB p))).length = 27 ∧
    (values (translated shift (familyA p))).Nodup ∧
    (values (translated shift (familyB p))).Nodup ∧
    SameIntegerTripleSums (translated shift (familyA p))
      (translated shift (familyB p)) :=
  ⟨values_length _, values_length _, ha, hb,
    every_translated_parameter_collision shift p⟩

def exampleParameters : Vec := (1,3,9,27,81)
def exampleA : Index → Int := translated 163 (familyA exampleParameters)
def exampleB : Index → Int := translated 163 (familyB exampleParameters)

theorem exampleA_matches (i : Index) : exampleA i = (A i : Int) := by
  revert i
  decide

theorem exampleB_matches_reverse :
    values exampleB = ((indices.map B).reverse).map (fun n : Nat => (n : Int)) := by decide

theorem exampleA_nodup : (values exampleA).Nodup := by decide
theorem exampleB_nodup : (values exampleB).Nodup := by decide
theorem example_positive : ∀ i : Index, 0 < exampleA i ∧ 0 < exampleB i := by decide

theorem example_different_sets : ¬ (∀ x : Int,
    (∃ i : Index, exampleA i = x) ↔ (∃ i : Index, exampleB i = x)) := by
  intro h
  have hA : ∃ i : Index, exampleA i = 44 := ⟨1, rfl⟩
  obtain ⟨i, hi⟩ := (h 44).mp hA
  have hn : ∀ j : Index, exampleB j ≠ 44 := by decide
  exact hn i hi

theorem example_is_nontrivial_collision :
    (values exampleA).length = 27 ∧ (values exampleB).length = 27 ∧
    (values exampleA).Nodup ∧ (values exampleB).Nodup ∧
    (∀ i : Index, 0 < exampleA i ∧ 0 < exampleB i) ∧
    SameIntegerTripleSums exampleA exampleB ∧
    ¬ (∀ x : Int, (∃ i : Index, exampleA i = x) ↔
      (∃ i : Index, exampleB i = x)) :=
  ⟨values_length _, values_length _, exampleA_nodup, exampleB_nodup,
    example_positive, every_translated_parameter_collision 163 exampleParameters,
    example_different_sets⟩

#print axioms vector_triple_sums_perm
#print axioms every_additive_image_collision
#print axioms every_parameter_collision
#print axioms every_translated_parameter_collision
#print axioms example_is_nontrivial_collision

end JSP399Parametric
