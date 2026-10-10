import IGSIII34.Percolation.Network
import IGSIII34.Resistance.Reindex
import Universality.Graph.NetworkEquivalence

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Percolation
noncomputable section
open Resistance Resistance.FiniteNetwork

variable {firstVertices firstEdges secondVertices secondEdges : ℕ}
  {first : Universality.FiniteNetwork firstVertices firstEdges}
  {second : Universality.FiniteNetwork secondVertices secondEdges}

def networkEquivalenceOpenEdges (equivalence : first.NetworkEquivalence second)
    (configuration : Universality.FiniteNetwork.Configuration firstEdges) :
    {edge : Fin firstEdges // configuration edge = true} ≃
      {edge : Fin secondEdges // equivalence.configuration configuration edge = true} :=
  equivalence.edge.subtypeEquiv (p := fun edge => configuration edge = true)
    (q := fun edge => equivalence.configuration configuration edge = true) (by
      intro edge
      simp only [Universality.FiniteNetwork.NetworkEquivalence.configuration, Equiv.coe_fn_mk,
        Equiv.symm_apply_apply])

theorem networkEquivalence_conductance (equivalence : first.NetworkEquivalence second)
    (configuration : Universality.FiniteNetwork.Configuration firstEdges)
    (resistance : {edge : Fin firstEdges // configuration edge = true} → ℝ) :
    (network second (equivalence.configuration configuration)).effectiveConductance
        (fun edge => resistance ((networkEquivalenceOpenEdges equivalence configuration).symm edge)) =
      (network first configuration).effectiveConductance resistance := by
  apply effectiveConductance_reindex (network first configuration)
    (network second (equivalence.configuration configuration)) equivalence.vertex
    (networkEquivalenceOpenEdges equivalence configuration)
  · intro edge
    exact equivalence.endpoint edge.val
  · exact equivalence.source.symm
  · exact equivalence.target.symm

theorem networkEquivalence_resistance (equivalence : first.NetworkEquivalence second)
    (configuration : Universality.FiniteNetwork.Configuration firstEdges)
    (crosses : first.crosses configuration = true)
    (resistance : {edge : Fin firstEdges // configuration edge = true} → ℝ)
    (positive : ∀ edge, 0 < resistance edge) :
    (network second (equivalence.configuration configuration)).effectiveResistance
        (fun edge => resistance ((networkEquivalenceOpenEdges equivalence configuration).symm edge)) =
      (network first configuration).effectiveResistance resistance := by
  have equality := networkEquivalence_conductance equivalence configuration resistance
  rw [effectiveConductance_eq_reciprocalResistance _
      (connected_of_crosses _ _ ((equivalence.crosses configuration).trans crosses))
      (fun edge => positive ((networkEquivalenceOpenEdges equivalence configuration).symm edge)),
    effectiveConductance_eq_reciprocalResistance _ (connected_of_crosses _ _ crosses) positive] at equality
  exact inv_injective (by simpa only [one_div] using equality)

end
end IGSIII34.Percolation
