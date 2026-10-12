import IGSIII4.SpectralDensity.ActualMomentFiniteLaw20261012
import IGSIII34.Percolation.GenerationMean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Probability

theorem actual_generation_weighted_cell_observable
    (blocks paths interior : ℕ) (pathsPositive : 0 < paths) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (critical : (network blocks paths interior).reliability probability = probability)
    (depth : ℕ) (observable : ℝ → ℝ) :
    weightedCellObservable blocks paths interior probability
      (((rule blocks paths interior).generation depth).network.conditionalCellWeight probability true)
      (positiveNormalizedResistance ((rule blocks paths interior).generation depth).network probability)
      observable =
    finiteMean (((rule blocks paths interior).generation (depth + 1)).network.conditionalCellWeight probability true)
      (fun configuration => observable
        (unitConfigurationResistance ((rule blocks paths interior).generation (depth + 1)).network configuration /
          conditionalMeanResistance ((rule blocks paths interior).generation depth).network probability)) := by
  have meanPositive := generation_conditionalMeanResistance_positive (rule blocks paths interior)
    (classical blocks paths interior pathsPositive) probability positive belowOne critical depth
  have identity := normalized_generation_block_resistance_observable (rule blocks paths interior)
    probability positive belowOne critical 0 depth meanPositive observable
  rw [show 0 + depth + 1 = depth + 1 by omega] at identity
  simpa only [Rule.generation, weightedCellObservable, finiteMean,
    IGSIII34.Probability.productWeight, IGSIII34.Probability.tupleWeight,
    IGSIII.Probability.tupleWeight] using identity.symm

theorem actual_generation_weighted_cell_mean
    (blocks paths interior : ℕ) (pathsPositive : 0 < paths) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (critical : (network blocks paths interior).reliability probability = probability) (depth : ℕ) :
    weightedCellMean blocks paths interior probability
      (((rule blocks paths interior).generation depth).network.conditionalCellWeight probability true)
      (positiveNormalizedResistance ((rule blocks paths interior).generation depth).network probability) =
    conditionalMeanResistance ((rule blocks paths interior).generation (depth + 1)).network probability /
      conditionalMeanResistance ((rule blocks paths interior).generation depth).network probability := by
  unfold weightedCellMean
  rw [actual_generation_weighted_cell_observable blocks paths interior pathsPositive probability
    positive belowOne critical depth id]
  simp only [id_eq, div_eq_mul_inv]
  rw [finiteMean_mul_const, finiteMean_conditional_unitResistance]

theorem actual_generation_weighted_cell_second_moment
    (blocks paths interior : ℕ) (pathsPositive : 0 < paths) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (critical : (network blocks paths interior).reliability probability = probability) (depth : ℕ) :
    weightedCellSecondMoment blocks paths interior probability
      (((rule blocks paths interior).generation depth).network.conditionalCellWeight probability true)
      (positiveNormalizedResistance ((rule blocks paths interior).generation depth).network probability) =
    finiteMean (((rule blocks paths interior).generation (depth + 1)).network.conditionalCellWeight probability true)
      (fun configuration => unitConfigurationResistance
        ((rule blocks paths interior).generation (depth + 1)).network configuration ^ 2) /
      conditionalMeanResistance ((rule blocks paths interior).generation depth).network probability ^ 2 := by
  unfold weightedCellSecondMoment
  rw [actual_generation_weighted_cell_observable blocks paths interior pathsPositive probability
    positive belowOne critical depth (fun value => value ^ 2)]
  simp only [div_eq_mul_inv, mul_pow, inv_pow]
  rw [finiteMean_mul_const]

end
end IGSIII4.SpectralDensity.ActualFamily
