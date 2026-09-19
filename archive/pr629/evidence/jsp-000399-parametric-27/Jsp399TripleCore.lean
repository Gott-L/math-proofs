import Std

/-!
Shared complete enumeration of triples on 27 indices and kernel-checkable
permutation-preserving merge helpers for JSP-000399 / Erdos 494.
Written with OpenAI Codex assistance, 2026-09-17. MIT license.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JSP399TwentySeven

abbrev Index := Fin 27
abbrev Triple := Index × Index × Index

def indices : List Index := List.ofFn (fun i : Index => i)

theorem mem_indices (i : Index) : i ∈ indices := by
  exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem indices_nodup : indices.Nodup := by decide

/-- Pairing each outer index with its own distinct inner indices gives
a list with no repeated pairs. -/
theorem nodup_tagged_flatMap {α β : Type} (l : List α) (f : α → List β)
    (hl : l.Nodup) (hf : ∀ a ∈ l, (f a).Nodup) :
    (l.flatMap (fun a => (f a).map (fun b => (a,b)))).Nodup := by
  apply List.pairwise_flatMap.mpr
  constructor
  · intro a ha
    apply List.pairwise_map.mpr
    exact (hf a ha).imp (by intro x y hxy heq; exact hxy (congrArg Prod.snd heq))
  · apply hl.imp
    intro a b hab x hx y hy heq
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hy
    exact hab (congrArg Prod.fst heq)

def tails (i : Index) : List (Index × Index) :=
  indices.flatMap (fun j =>
    (indices.filter (fun k => decide (i < j ∧ j < k))).map (fun k => (j,k)))

/-- Each three-element index subset is represented in increasing order. -/
def triples : List Triple :=
  indices.flatMap (fun i => (tails i).map (fun p => (i,p)))

theorem triples_complete (i j k : Index) :
    (i,j,k) ∈ triples ↔ i < j ∧ j < k := by
  simp [triples, tails, List.mem_flatMap, List.mem_map, List.mem_filter,
    mem_indices, Prod.mk.injEq]

theorem triples_nodup : triples.Nodup := by
  apply nodup_tagged_flatMap indices tails indices_nodup
  intro i _
  apply nodup_tagged_flatMap indices _ indices_nodup
  intro j _
  exact indices_nodup.filter _

theorem triples_length : triples.length = 2925 := by decide

/-- Every triple contributes an entry; repeated numerical sums are retained. -/
def tripleSums (a : Index → Nat) : List Nat :=
  triples.map (fun p => a p.1 + a p.2.1 + a p.2.2)

def SameTripleSums (a b : Index → Nat) : Prop :=
  (tripleSums a).Perm (tripleSums b)

/-- Structurally recursive merge; exhausted fuel safely appends the remainder. -/
def mergeWithFuel {α : Type} (le : α → α → Bool) : Nat → List α → List α → List α
  | 0, xs, ys => xs ++ ys
  | _+1, [], ys => ys
  | _+1, xs, [] => xs
  | n+1, x::xs, y::ys =>
    if le x y then x :: mergeWithFuel le n xs (y::ys)
    else y :: mergeWithFuel le n (x::xs) ys

theorem mergeWithFuel_perm {α : Type} (le : α → α → Bool) (fuel : Nat)
    (xs ys : List α) : (mergeWithFuel le fuel xs ys).Perm (xs ++ ys) := by
  induction fuel generalizing xs ys with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    cases xs with
    | nil => simp [mergeWithFuel]
    | cons x xs =>
      cases ys with
      | nil => simp [mergeWithFuel]
      | cons y ys =>
        simp only [mergeWithFuel]
        split
        · exact (ih xs (y::ys)).cons x
        · exact ((ih (x::xs) ys).cons y).trans List.perm_middle.symm

/-- A fuel-bounded merge computation. Permutation preservation holds for
every fuel value, independently of whether the result is fully sorted. -/
def sortWithFuel {α : Type} (le : α → α → Bool) : Nat → List α → List α
  | 0, xs => xs
  | n+1, xs =>
    let m := xs.length / 2
    mergeWithFuel le xs.length
      (sortWithFuel le n (xs.take m)) (sortWithFuel le n (xs.drop m))

theorem sortWithFuel_perm {α : Type} (le : α → α → Bool) (fuel : Nat)
    (xs : List α) : (sortWithFuel le fuel xs).Perm xs := by
  induction fuel generalizing xs with
  | zero => exact List.Perm.refl _
  | succ n ih =>
    unfold sortWithFuel
    have h := mergeWithFuel_perm le xs.length
      (sortWithFuel le n (xs.take (xs.length / 2)))
      (sortWithFuel le n (xs.drop (xs.length / 2)))
    have hi := (ih (xs.take (xs.length / 2))).append (ih (xs.drop (xs.length / 2)))
    have hc := h.trans hi
    simpa only [List.take_append_drop] using hc


#print axioms triples_complete
#print axioms triples_nodup
#print axioms triples_length
#print axioms sortWithFuel_perm

end JSP399TwentySeven
