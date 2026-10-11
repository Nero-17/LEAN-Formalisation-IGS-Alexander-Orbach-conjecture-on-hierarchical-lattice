import Universality.Matrix.WheatstoneSpectrum
import Universality.Percolation.OppositeWheatstoneCounts
import Universality.Percolation.LocalMassResponse

namespace Universality
noncomputable section
open Matrix FiniteNetwork

def oppositeWheatstoneMassMatrix : Matrix LiveState LiveState ℝ :=
  oppositeWheatstoneNetwork.massMatrix (1 / 2)

theorem oppositeWheatstone_reliability_half :
    oppositeWheatstoneNetwork.reliability (1 / 2) = 1 / 2 := by
  rw [← conditioningProbability_connected, conditioningProbability_half,
    oppositeWheatstone_exact_counts.1]
  norm_num

theorem oppositeWheatstoneMassMatrix_entry (σ τ : LiveState) :
    oppositeWheatstoneMassMatrix σ τ = (oppositeWheatstoneCountTable σ τ : ℝ) / 4096 := by
  simp only [oppositeWheatstoneMassMatrix, massMatrix_half, oppositeWheatstone_fair_mass,
    Rat.cast_div, Rat.cast_natCast]
  norm_num

theorem oppositeWheatstoneMassMatrix_pos (σ τ : LiveState) :
    0 < oppositeWheatstoneMassMatrix σ τ := by
  cases σ <;> cases τ <;>
    norm_num [oppositeWheatstoneMassMatrix_entry, oppositeWheatstoneCountTable]

theorem oppositeWheatstoneMassMatrix_preservesMassPlane :
    PreservesMassPlane oppositeWheatstoneMassMatrix := by
  apply preservesMassPlane_of_entries <;>
    norm_num [oppositeWheatstoneMassMatrix_entry, oppositeWheatstoneCountTable]

theorem oppositeWheatstoneMassMatrix_block :
    massPlaneBlock oppositeWheatstoneMassMatrix =
      (Rat.castHom ℝ).mapMatrix oppositeWheatstoneBlock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [massPlaneBlock, oppositeWheatstoneMassMatrix_entry, oppositeWheatstoneCountTable,
      oppositeWheatstoneBlock, RingHom.mapMatrix_apply, Matrix.map_apply]

theorem oppositeWheatstone_full_spectralRadius :
    spectralRadius ℂ (oppositeWheatstoneMassMatrix.map Complex.ofReal) =
      ENNReal.ofReal (positiveRoot ((Rat.castHom ℝ).mapMatrix oppositeWheatstoneBlock)) := by
  rw [← oppositeWheatstoneMassMatrix_block]
  apply massPlane_spectralRadius
  · exact fun σ τ => (oppositeWheatstoneMassMatrix_pos σ τ).le
  · exact oppositeWheatstoneMassMatrix_preservesMassPlane
  · intro i j
    rw [oppositeWheatstoneMassMatrix_block]
    fin_cases i <;> fin_cases j <;>
      norm_num [oppositeWheatstoneBlock, RingHom.mapMatrix_apply, Matrix.map_apply]

end
end Universality
