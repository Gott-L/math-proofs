import JoinBound
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith

/-!
An elementary maximum-degree bound for JSP-000897 / Erdos problem 1079.
The only extremal-number input is the independently proved join construction.
No Turan graph, Turan theorem, or assumed formula for an extremal number is used.
This new implementation was written after reading an earlier formalization;
it is not a clean-room or first-formalization claim.
-/

open Finset
open scoped BigOperators

namespace GottL897

/-- The balanced product is within one quarter of the square, including odd orders. -/
theorem sq_le_four_mul_balanced_product_add_one (n : ℕ) :
    n ^ 2 ≤ 4 * (n / 2 * (n - n / 2)) + 1 := by
  have hdiv := Nat.mod_add_div n 2
  have hmod : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hmod with hzero | hone
  · have hn : n = 2 * (n / 2) := by omega
    have hsub : n - n / 2 = n / 2 := by omega
    rw [hsub]
    nlinarith
  · have hn : n = 2 * (n / 2) + 1 := by omega
    have hsub : n - n / 2 = n / 2 + 1 := by omega
    rw [hsub]
    nlinarith

/-- Dropping the nonnegative old component in the join bound gives this lower bound. -/
theorem balanced_product_le_clique_extremal {n r : ℕ} (hr : 3 ≤ r) :
    n / 2 * (n - n / 2) ≤
      SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) := by
  have hsplit := clique_extremal_join_le (n := n) (d := n / 2) hr
    (Nat.div_le_self n 2)
  omega

/-- Any graph with at least the balanced-product edge count has degree at least n/2. -/
theorem card_le_twice_maxDegree_of_balanced_edges {n : ℕ} (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : n / 2 * (n - n / 2) ≤ G.edgeFinset.card) :
    n ≤ 2 * G.maxDegree := by
  have hdegree : 2 * G.edgeFinset.card ≤ n * G.maxDegree := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    calc
      ∑ v, G.degree v ≤ ∑ _v : Fin n, G.maxDegree := by
        apply Finset.sum_le_sum
        intro v _hv
        exact G.degree_le_maxDegree v
      _ = n * G.maxDegree := by simp
  have hsquare := sq_le_four_mul_balanced_product_add_one n
  by_contra hnot
  have hstrict : 2 * G.maxDegree + 1 ≤ n := by omega
  have hmul := Nat.mul_le_mul_left n hstrict
  nlinarith

/-- The full clique-extremal threshold implies a uniform linear maximum degree. -/
theorem card_le_twice_maxDegree_of_extremal_threshold {n r : ℕ}
    (hr : 4 ≤ r) (hn : 2 ≤ n) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj]
    (hG : SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r)) ≤
      G.edgeFinset.card) :
    n ≤ 2 * G.maxDegree := by
  apply card_le_twice_maxDegree_of_balanced_edges hn G
  exact (balanced_product_le_clique_extremal (by omega : 3 ≤ r)).trans hG

end GottL897
