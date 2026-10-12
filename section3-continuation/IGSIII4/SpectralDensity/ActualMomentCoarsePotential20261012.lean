import IGSIII4.SpectralDensity.ActualMomentWeightedCurrents20261012

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {blocks paths interior : ℕ}

def coarseConfiguration (configuration : Edge blocks paths interior → Bool) : Fin (blocks + 2) → Bool :=
  Fin.cases (configuration (.inl 2))
    (Fin.lastCases (configuration (.inl 3))
      (fun block => decide (∃ path : Fin paths, ∀ edge : Fin (interior + 2),
        configuration (.inr (block, path, edge)) = true)))

def coarseResistance (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) : Fin (blocks + 2) → ℝ :=
  Fin.cases (resistance (.inl 2))
    (Fin.lastCases (resistance (.inl 3)) (blockResistance configuration resistance))

theorem coarseConfiguration_complete20261012 (configuration : Edge blocks paths interior → Bool) :
    (∀ edge, coarseConfiguration configuration edge = true) ↔ LongCrosses configuration := by
  rw [Fin.forall_iff_succ]
  simp only [coarseConfiguration, Fin.cases_zero, Fin.cases_succ]
  rw [Fin.forall_iff_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, decide_eq_true_eq]
  unfold LongCrosses ChainCrosses
  tauto

theorem coarseResistance_sum20261012 (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) :
    (∑ edge, coarseResistance configuration resistance edge) = longResistance configuration resistance := by
  rw [Fin.sum_univ_succ]
  simp only [coarseResistance, Fin.cases_zero, Fin.cases_succ]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last, longResistance]
  ring

def coarsePotential (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) : Fin (blocks + 3) → ℝ :=
  openPathPotential (coarseConfiguration configuration) (coarseResistance configuration resistance)
    (longBranchCurrent configuration resistance) (circuitVoltage configuration resistance) 0

def weightedJunctionPotential (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (junction : Fin (blocks + 1)) : ℝ :=
  coarsePotential configuration resistance junction.castSucc.succ

theorem coarsePotential_right20261012 (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge) :
    coarsePotential configuration resistance (Fin.last (blocks + 2)) = 0 := by
  apply openPathPotential_right20261012
  intro complete
  rw [coarseResistance_sum20261012, sub_zero]
  exact longBranchCurrent_voltage20261012 configuration resistance positive
    ((coarseConfiguration_complete20261012 configuration).mp complete)

theorem coarsePotential_ohm20261012 (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (edge : Fin (blocks + 2))
    (opened : coarseConfiguration configuration edge = true) :
    coarsePotential configuration resistance edge.castSucc -
      coarsePotential configuration resistance edge.succ =
        coarseResistance configuration resistance edge * longBranchCurrent configuration resistance := by
  apply openPathPotential_ohm20261012
  · intro failed
    have noLong : ¬LongCrosses configuration :=
      fun complete => failed ((coarseConfiguration_complete20261012 configuration).mpr complete)
    simp [longBranchCurrent, longConductance, noLong]
  · exact opened

theorem weightedJunctionPotential_left_exterior20261012
    (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ)
    (opened : configuration (.inl 2) = true) :
    resistance (.inl 2) * longBranchCurrent configuration resistance =
      circuitVoltage configuration resistance - weightedJunctionPotential configuration resistance 0 := by
  have identity := coarsePotential_ohm20261012 configuration resistance (0 : Fin (blocks + 2))
    (by simpa [coarseConfiguration] using opened)
  simpa [coarsePotential, coarseResistance, weightedJunctionPotential, openPathPotential_left20261012] using identity.symm

theorem weightedJunctionPotential_right_exterior20261012
    (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (opened : configuration (.inl 3) = true) :
    resistance (.inl 3) * longBranchCurrent configuration resistance =
      weightedJunctionPotential configuration resistance (Fin.last blocks) := by
  have identity := coarsePotential_ohm20261012 configuration resistance (Fin.last (blocks + 1))
    (by
      rw [show Fin.last (blocks + 1) = (Fin.last blocks).succ from rfl]
      simpa only [coarseConfiguration, Fin.cases_succ, Fin.lastCases_last] using opened)
  have lastSuccessor : (Fin.last (blocks + 1)).succ = Fin.last (blocks + 2) := rfl
  rw [lastSuccessor, coarsePotential_right20261012 configuration resistance positive, sub_zero] at identity
  have junctionIndex : (Fin.last (blocks + 1)).castSucc = (Fin.last blocks).castSucc.succ := by apply Fin.ext; rfl
  rw [junctionIndex] at identity
  rw [show Fin.last (blocks + 1) = (Fin.last blocks).succ from rfl] at identity
  simpa only [coarseResistance, Fin.cases_succ, Fin.lastCases_last, weightedJunctionPotential] using identity.symm

theorem weightedJunctionPotential_block20261012
    (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (block : Fin blocks)
    (opened : ∃ path : Fin paths, ∀ edge : Fin (interior + 2),
      configuration (.inr (block, path, edge)) = true) :
    weightedJunctionPotential configuration resistance block.castSucc -
      weightedJunctionPotential configuration resistance block.succ =
        blockResistance configuration resistance block * longBranchCurrent configuration resistance := by
  have identity := coarsePotential_ohm20261012 configuration resistance block.castSucc.succ
    (by simpa [coarseConfiguration] using opened)
  have leftIndex : block.castSucc.succ.castSucc = block.castSucc.castSucc.succ := by apply Fin.ext; rfl
  have rightIndex : block.castSucc.succ.succ = block.succ.castSucc.succ := by apply Fin.ext; rfl
  rw [leftIndex, rightIndex] at identity
  simpa [coarseResistance, weightedJunctionPotential] using identity

end
end IGSIII4.SpectralDensity.ActualFamily
