/- Direct composition of the inherited cycle bridge with the proved
minimal-counterexample configuration exclusion. No finite Folkman premise is
assumed here; the remaining explicit input is the actual minimal-counterexample
predicate. Local integration by Codex/B under Gott-L's direction. -/
import E922EvenCycleBridge

namespace Erdos922Recolor.EvenCycleBridge

theorem no_induced_even_cycle_iso_of_orderMinimalCounterexample
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hmin : Erdos922FullB.IsOrderMinimalCounterexample G) :
    ¬ ∃ (C : Set V) (p : ℕ), 2 ≤ p ∧
      Nonempty (G.induce C ≃g SimpleGraph.cycleGraph (2 * p)) := by
  classical
  exact no_induced_even_cycle_iso_of_no_configuration G
    (Erdos922.EvenHole.no_configuration_of_orderMinimalCounterexample G hmin)

end Erdos922Recolor.EvenCycleBridge
