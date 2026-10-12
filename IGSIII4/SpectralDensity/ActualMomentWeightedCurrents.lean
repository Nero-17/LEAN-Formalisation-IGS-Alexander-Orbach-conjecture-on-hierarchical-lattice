import IGSIII4.SpectralDensity.ActualMomentCircuitAlgebra

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {blocks paths interior : ℕ}

def weightedCircuitCurrent (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) : Edge blocks paths interior → ℝ :=
  circuitCurrent blocks paths interior (shortBranchCurrent configuration resistance)
    (longBranchCurrent configuration resistance) (weightedPathCurrent configuration resistance)

theorem weightedCircuitCurrent_unit_flow (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (crosses : CircuitCrosses blocks paths interior configuration) :
    weightedCircuitCurrent configuration resistance ∈ (fullElectricalNetwork blocks paths interior).unitFlows :=
  circuitCurrent_unit_flow _ _ _
    (weightedPathCurrent_block_sum configuration resistance positive)
    (branchCurrent_total configuration resistance positive crosses)

theorem weightedCircuitCurrent_closed_zero (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (edge : Edge blocks paths interior)
    (closed : configuration edge ≠ true) : weightedCircuitCurrent configuration resistance edge = 0 := by
  rcases edge with edge | ⟨block, path, edge⟩
  · fin_cases edge
    · have failed : ¬ShortCrosses configuration := fun opened => closed opened.1
      simp [weightedCircuitCurrent, circuitCurrent, shortBranchCurrent, shortConductance, failed]
    · have failed : ¬ShortCrosses configuration := fun opened => closed opened.2
      simp [weightedCircuitCurrent, circuitCurrent, shortBranchCurrent, shortConductance, failed]
    · have failed : ¬LongCrosses configuration := fun opened => closed opened.1
      simp [weightedCircuitCurrent, circuitCurrent, longBranchCurrent, longConductance, failed]
    · have failed : ¬LongCrosses configuration := fun opened => closed opened.2.1
      simp [weightedCircuitCurrent, circuitCurrent, longBranchCurrent, longConductance, failed]
  · have failed : ¬∀ other : Fin (interior + 2), configuration (.inr (block, path, other)) = true :=
      fun opened => closed (opened edge)
    simp [weightedCircuitCurrent, circuitCurrent, weightedPathCurrent, pathConductance, failed]

theorem shortBranchCurrent_voltage (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (crosses : ShortCrosses configuration) :
    shortBranchCurrent configuration resistance * shortResistance resistance =
      circuitVoltage configuration resistance := by
  have nonzero : shortResistance resistance ≠ 0 :=
    ne_of_gt (add_pos (positive (.inl 0)) (positive (.inl 1)))
  simp only [shortBranchCurrent, shortConductance, crosses, ↓reduceIte]
  rw [mul_assoc, inv_mul_cancel₀ nonzero, mul_one]

theorem longBranchCurrent_voltage (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (crosses : LongCrosses configuration) :
    longBranchCurrent configuration resistance * longResistance configuration resistance =
      circuitVoltage configuration resistance := by
  have nonzero := ne_of_gt (longResistance_positive configuration resistance positive)
  simp only [longBranchCurrent, longConductance, crosses, ↓reduceIte]
  rw [mul_assoc, inv_mul_cancel₀ nonzero, mul_one]

theorem weightedPathCurrent_voltage (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (block : Fin blocks) (path : Fin paths)
    (crosses : ∀ edge : Fin (interior + 2), configuration (.inr (block, path, edge)) = true) :
    weightedPathCurrent configuration resistance block path * pathResistance resistance block path =
      longBranchCurrent configuration resistance * blockResistance configuration resistance block := by
  have nonzero := ne_of_gt (pathResistance_positive resistance positive block path)
  simp only [weightedPathCurrent, pathConductance, crosses, implies_true, ↓reduceIte]
  rw [mul_assoc, inv_mul_cancel₀ nonzero, mul_one]

end
end IGSIII4.SpectralDensity.ActualFamily
