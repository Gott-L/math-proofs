import EGPGraph

-- Fully expanded local finite-vertex statement; no assumed decomposition.
example {V : Type*} (S : Finset V) (R : V → V → Prop)
    (hs : ∀ ⦃a b⦄, R a b → R b a) (hi : ∀ a, ¬R a a) :
    ∃ P : Finset (Finset V),
      ((∀ p ∈ P, p ⊆ S ∧ (p.card = 2 ∨ p.card = 3) ∧
          ∀ a ∈ p, ∀ b ∈ p, a ≠ b → R a b) ∧
        ∀ a ∈ S, ∀ b ∈ S, R a b → ∃! p, p ∈ P ∧ a ∈ p ∧ b ∈ p) ∧
      P.card ≤ S.card ^ 2 / 4 := EGP.erdos_goodman_posa S R hs hi

example (n : ℕ) (R : Fin n → Fin n → Prop)
    (hs : ∀ ⦃a b⦄, R a b → R b a) (hi : ∀ a, ¬R a a) :
    ∃ P : Finset (Finset (Fin n)), P.card ≤ n ^ 2 / 4 ∧
      (∀ p ∈ P, (p.card = 2 ∨ p.card = 3) ∧
        ∀ a ∈ p, ∀ b ∈ p, a ≠ b → R a b) ∧
      (∀ a b, R a b → ∃! p, p ∈ P ∧ a ∈ p ∧ b ∈ p) :=
  EGP.finite_relation_partition n R hs hi

-- The ordinary Mathlib graph endpoint quantifies over every finite simple graph.
example {V : Type*} [Fintype V] (G : SimpleGraph V) :
    ∃ P : Finset (Finset V), P.card ≤ Fintype.card V ^ 2 / 4 ∧
      (∀ p ∈ P, (p.card = 2 ∨ p.card = 3) ∧
        ∀ a ∈ p, ∀ b ∈ p, a ≠ b → G.Adj a b) ∧
      (∀ a b, G.Adj a b → ∃! p, p ∈ P ∧ a ∈ p ∧ b ∈ p) :=
  EGP.simple_graph_partition G

example (n : ℕ) : n ^ 2 / 4 + (n + 1) / 2 = (n + 1) ^ 2 / 4 :=
  EGP.floor_quarter_square_step n
