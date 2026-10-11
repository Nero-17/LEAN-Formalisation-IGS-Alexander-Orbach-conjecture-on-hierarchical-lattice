import Universality.Matrix.MassPlane
import Universality.Percolation.ReliabilityDerivative

namespace Universality
noncomputable section
open Matrix FiniteNetwork

def wheatstoneMassMatrix : Matrix LiveState LiveState ℝ :=
  wheatstoneNetwork.massMatrix (1 / 2)

theorem wheatstoneMassMatrix_entry (σ τ : LiveState) :
    wheatstoneMassMatrix σ τ = (wheatstoneCountTable σ τ : ℝ) / 16 := by
  simp only [wheatstoneMassMatrix, massMatrix_half, wheatstone_fair_mass,
    Rat.cast_div, Rat.cast_natCast]
  norm_num

theorem wheatstoneMassMatrix_pos (σ τ : LiveState) : 0 < wheatstoneMassMatrix σ τ := by
  cases σ <;> cases τ <;> norm_num [wheatstoneMassMatrix_entry, wheatstoneCountTable]

theorem wheatstoneMassMatrix_preservesMassPlane : PreservesMassPlane wheatstoneMassMatrix := by
  apply preservesMassPlane_of_entries <;>
    norm_num [wheatstoneMassMatrix_entry, wheatstoneCountTable]

theorem wheatstoneMassMatrix_block :
    massPlaneBlock wheatstoneMassMatrix = (Rat.castHom ℝ).mapMatrix wheatstoneBlock := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [massPlaneBlock, wheatstoneMassMatrix_entry, wheatstoneCountTable,
      wheatstoneBlock, RingHom.mapMatrix_apply, Matrix.map_apply]

def pivotalLeftVector : LiveState → ℝ
  | .connected => 0
  | .both => -1 / 2
  | .single => 1

def wheatstonePivotalRightVector : LiveState → ℝ
  | .connected => 1
  | .both | .single => -1

theorem wheatstone_pivotal_left_eigenvector :
    pivotalLeftVector ᵥ* wheatstoneMassMatrix =
      deriv wheatstoneNetwork.reliability (1 / 2) • pivotalLeftVector := by
  rw [wheatstone_deriv_half]
  ext σ
  cases σ <;> norm_num [Matrix.vecMul, dotProduct, sum_liveState,
    pivotalLeftVector, wheatstoneMassMatrix_entry, wheatstoneCountTable]

theorem wheatstone_pivotal_right_eigenvector :
    wheatstoneMassMatrix *ᵥ wheatstonePivotalRightVector =
      deriv wheatstoneNetwork.reliability (1 / 2) • wheatstonePivotalRightVector := by
  rw [wheatstone_deriv_half]
  ext σ
  cases σ <;> norm_num [Matrix.mulVec, dotProduct, sum_liveState,
    wheatstonePivotalRightVector, wheatstoneMassMatrix_entry, wheatstoneCountTable]

theorem wheatstone_full_spectralRadius :
    spectralRadius ℂ (wheatstoneMassMatrix.map Complex.ofReal) =
      ENNReal.ofReal (positiveRoot ((Rat.castHom ℝ).mapMatrix wheatstoneBlock)) := by
  rw [← wheatstoneMassMatrix_block]
  apply massPlane_spectralRadius
  · exact fun σ τ => (wheatstoneMassMatrix_pos σ τ).le
  · exact wheatstoneMassMatrix_preservesMassPlane
  · intro i j
    rw [wheatstoneMassMatrix_block]
    fin_cases i <;> fin_cases j <;>
      norm_num [wheatstoneBlock, RingHom.mapMatrix_apply, Matrix.map_apply]

end
end Universality
