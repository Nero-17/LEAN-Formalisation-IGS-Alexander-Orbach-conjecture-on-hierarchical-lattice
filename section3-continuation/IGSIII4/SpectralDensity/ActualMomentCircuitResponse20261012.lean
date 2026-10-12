import IGSIII4.SpectralDensity.ActualMomentCoarsePotential20261012
import IGSIII4.SpectralDensity.ActualMomentCircuitPotential20261012

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {blocks paths interior : ℕ}

/-- The actual full open graph has the series/parallel weighted resistance.
Every local voltage and Kirchhoff identity is constructed from the input
edge resistances and open configuration, rather than assumed. -/
theorem actual_typed_circuit_resistance20261012
    (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (crosses : CircuitCrosses blocks paths interior configuration) :
    (openElectricalNetwork blocks paths interior configuration).effectiveResistance
      (fun edge => resistance edge.val) = circuitVoltage configuration resistance := by
  have shortComplete : (∀ edge : Fin 2, configuration (shortEdge edge) = true) ↔
      ShortCrosses configuration := by
    constructor
    · intro complete
      exact ⟨complete 0, complete 1⟩
    · intro complete edge
      fin_cases edge
      · exact complete.1
      · exact complete.2
  apply actual_circuit_voltage_of_local_identities20261012 configuration resistance positive
    (circuitVoltage configuration resistance) (shortBranchCurrent configuration resistance)
    (longBranchCurrent configuration resistance) (weightedJunctionPotential configuration resistance)
    (weightedPathCurrent configuration resistance)
  · exact weightedPathCurrent_block_sum20261012 configuration resistance positive
  · exact branchCurrent_total20261012 configuration resistance positive crosses
  · exact weightedCircuitCurrent_closed_zero20261012 configuration resistance
  · intro complete
    have identity := shortBranchCurrent_voltage20261012 configuration resistance positive (shortComplete.mp complete)
    simpa [shortResistance, Fin.sum_univ_succ, shortEdge] using identity
  · intro failed
    have noShort : ¬ShortCrosses configuration := fun complete => failed (shortComplete.mpr complete)
    simp [shortBranchCurrent, shortConductance, noShort]
  · intro block path complete
    have identity := weightedPathCurrent_voltage20261012 configuration resistance positive block path complete
    rw [mul_comm (longBranchCurrent configuration resistance), ← weightedJunctionPotential_block20261012
      configuration resistance block ⟨path, complete⟩] at identity
    exact identity
  · intro block path failed
    simp [weightedPathCurrent, pathConductance, failed]
  · exact weightedJunctionPotential_left_exterior20261012 configuration resistance
  · exact weightedJunctionPotential_right_exterior20261012 configuration resistance positive

end
end IGSIII4.SpectralDensity.ActualFamily
