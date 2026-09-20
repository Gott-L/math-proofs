import E922ChordlessCompat

/-!
A direct cardinality bridge for a finite spanning cycle, proved in Lean 4.19.
This replaces a later Hamiltonian-cycle API call; it assumes an actual cycle
and its full vertex-cardinality length, not the desired Folkman theorem.
Compatibility proof: Codex under Gott-L's project direction.
-/

namespace SimpleGraph.Walk
universe u
variable {V : Type u} {G : SimpleGraph V}

theorem IsCycle.mem_support_of_length_eq_card [Fintype V] {a : V}
    {p : G.Walk a a} (hp : p.IsCycle)
    (hlen : p.length = Fintype.card V) (w : V) : w ∈ p.support := by
  classical
  have ht : p.tail.IsPath := (isCycle_iff_isPath_tail_and_le_length.mp hp).1
  have hlength : p.tail.support.length = Fintype.card V := by
    rw [length_support, length_tail_add_one hp.not_nil, hlen]
  have hcard : p.tail.support.toFinset.card = Fintype.card V := by
    rw [List.toFinset_card_of_nodup ht.support_nodup, hlength]
  have huniv : p.tail.support.toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  have hw : w ∈ p.tail.support := by
    have hmem : w ∈ p.tail.support.toFinset := by rw [huniv]; exact Finset.mem_univ w
    exact List.mem_toFinset.mp hmem
  rw [support_tail p hp.not_nil] at hw
  exact List.mem_of_mem_tail hw

end SimpleGraph.Walk
