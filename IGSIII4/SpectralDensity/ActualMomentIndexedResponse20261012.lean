import IGSIII4.SpectralDensity.ActualMomentCircuitResponse20261012
import IGSIII4.SpectralDensity.ActualMomentReindex20261012
import IGSIII34.Percolation.Network

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
attribute [local instance] Classical.propDecidable
variable {blocks paths interior : ℕ}

def indexedOpenEdges (configuration : Edge blocks paths interior → Bool) :
    {edge : Edge blocks paths interior // configuration edge = true} ≃
      {edge : Fin (Fintype.card (Edge blocks paths interior)) //
        configuration ((Fintype.equivFin _).symm edge) = true} :=
  (Fintype.equivFin (Edge blocks paths interior)).subtypeEquiv (by
    intro edge
    simp only [Equiv.symm_apply_apply])

/-- The weighted circuit formula is a theorem about the very indexed network
used by the actual substitution and finite conditional resistance recursion. -/
theorem actual_indexed_circuit_resistance20261012
    (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (crosses : CircuitCrosses blocks paths interior configuration) :
    (IGSIII34.Percolation.network (network blocks paths interior)
      (fun edge => configuration ((Fintype.equivFin _).symm edge))).effectiveResistance
      (fun edge => resistance ((Fintype.equivFin _).symm edge.val)) =
        circuitVoltage configuration resistance := by
  have identity := IGSIII34.Resistance.FiniteNetwork.effectiveResistance_reindex20261012
    (openElectricalNetwork blocks paths interior configuration)
    (IGSIII34.Percolation.network (network blocks paths interior)
      (fun edge => configuration ((Fintype.equivFin _).symm edge)))
    (Fintype.equivFin (Vertex blocks paths interior)) (indexedOpenEdges configuration)
    (by
      intro edge
      simp [IGSIII34.Percolation.network, network, openElectricalNetwork, indexedOpenEdges])
    rfl rfl (fun edge => resistance edge.val)
  have weights : (fun edge => resistance ((indexedOpenEdges configuration).symm edge).val) =
      (fun edge => resistance ((Fintype.equivFin (Edge blocks paths interior)).symm edge.val)) := by
    funext edge
    rfl
  rw [weights] at identity
  exact identity.trans (actual_typed_circuit_resistance20261012 configuration resistance positive crosses)

end
end IGSIII4.SpectralDensity.ActualFamily
