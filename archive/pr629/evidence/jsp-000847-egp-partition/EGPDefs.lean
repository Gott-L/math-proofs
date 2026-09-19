/-
Copyright (c) 2026. Released under the Apache License, Version 2.0.
Project initiation, conception, objectives, planning and research direction: Gott-L.
Research, formal proof implementation and internal checks: Codex assistance.
Mathematical theorem: Erdos, Goodman and Posa (1966), Theorem 4.
-/
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases

namespace EGP

variable {V : Type*} [DecidableEq V]

noncomputable def neighbors (S : Finset V) (R : V → V → Prop) (v : V) : Finset V :=
  @Finset.filter V (R v) (Classical.decPred _) S

def Clique (R : V → V → Prop) (p : Finset V) : Prop :=
  ∀ a ∈ p, ∀ b ∈ p, a ≠ b → R a b

def MatchingOn (R : V → V → Prop) (N : Finset V) (M : Finset (Finset V)) : Prop :=
  (∀ e ∈ M, e.card = 2 ∧ e ⊆ N ∧ Clique R e) ∧
    (↑M : Set (Finset V)).Pairwise (fun e f => Disjoint e f)

def covered (M : Finset (Finset V)) : Finset V := M.biUnion id

def MaximalMatching (R : V → V → Prop) (N : Finset V)
    (M : Finset (Finset V)) : Prop :=
  ∀ a ∈ N, ∀ b ∈ N, a ∉ covered M → b ∉ covered M → ¬ R a b

def PartitionOn (S : Finset V) (R : V → V → Prop)
    (P : Finset (Finset V)) : Prop :=
  (∀ p ∈ P, p ⊆ S ∧ (p.card = 2 ∨ p.card = 3) ∧ Clique R p) ∧
    ∀ a ∈ S, ∀ b ∈ S, R a b → ∃! p, p ∈ P ∧ a ∈ p ∧ b ∈ p

def trim (R : V → V → Prop) (M : Finset (Finset V)) (a b : V) : Prop :=
  R a b ∧ ¬ ∃ e ∈ M, a ∈ e ∧ b ∈ e

end EGP
