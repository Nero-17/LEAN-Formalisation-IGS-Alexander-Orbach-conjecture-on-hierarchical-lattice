import IGSIII34.Percolation.NormalizedBlock
import IGSIII34.Percolation.GenerationRealMoments
import IGSIII.Chemical.SubstitutionPaths.NormalizedVariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Probability
open IGSIII.Chemical.Substitution
open scoped BigOperators

theorem generation_block_resistance_eq_electricalCell
    (rule : Rule) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation (coarse+fine+1)).edges) :
    unitConfigurationResistance (rule.generation (coarse+fine+1)).network configuration =
      electricalCell (rule.generation coarse).network (generationBlockCoarse rule coarse fine configuration)
        (fun edge => unitConfigurationResistance (rule.generation fine).network
          (generationBlockCells rule coarse fine configuration edge)) := by
  have identity := networkEquivalence_unit_resistance (rule.generationBlockDecomposition coarse fine) configuration
  have cellsIdentity : substitutionConfigurationEquiv (generationBlockCells rule coarse fine configuration) =
      (rule.generationBlockDecomposition coarse fine).configuration configuration := by
    simp [generationBlockCells, generationBlockCellsEquiv]
  rw [← identity, ← cellsIdentity]
  exact unitResistance_substitution_all _ _ _

theorem generation_block_normalized_resistance_joint_observable
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (coarse fine : ℕ)
    (response : Configuration (rule.generation coarse).edges → ℝ → ℝ) :
    finiteMean ((rule.generation (coarse+fine+1)).network.conditionalCellWeight parameter true)
      (fun configuration => response (generationBlockCoarse rule coarse fine configuration)
        (unitConfigurationResistance (rule.generation (coarse+fine+1)).network configuration /
          conditionalMeanResistance (rule.generation fine).network parameter)) =
      finiteMean ((rule.generation coarse).network.conditionalCellWeight parameter true) (fun outerConfiguration =>
        finiteMean (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
          (rule.generation fine).network.conditionalCellWeight parameter true)) (fun cells =>
            response outerConfiguration (electricalCell (rule.generation coarse).network outerConfiguration
              (fun edge => positiveNormalizedResistance (rule.generation fine).network parameter (cells edge))))) := by
  have meanPositive := generation_conditionalMeanResistance_positive rule classical parameter positive belowOne fixedPoint fine
  have law := actual_generation_block_observable rule parameter positive belowOne fixedPoint coarse fine
    (fun outerConfiguration cells => response outerConfiguration
      (electricalCell (rule.generation coarse).network outerConfiguration
        (fun edge => unitConfigurationResistance (rule.generation fine).network (cells edge)) /
          conditionalMeanResistance (rule.generation fine).network parameter))
  simp_rw [← generation_block_resistance_eq_electricalCell] at law
  refine law.trans ?_
  simp only [finiteMean, tupleWeight]
  apply Finset.sum_congr rfl
  intro outerConfiguration _
  congr 1
  have transport := actual_child_electrical_connected_product (rule.generation coarse).network
    (rule.generation fine).network parameter
    (by rwa [rule.generation_fixed_point parameter fixedPoint])
    (by rwa [rule.generation_fixed_point parameter fixedPoint]) outerConfiguration (response outerConfiguration)
  simp_rw [electricalCell_normalized_children _ _ parameter meanPositive] at transport
  exact transport

def electricalBlockConditionalMean
    (rule : Rule) (parameter : ℝ) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation coarse).edges) : ℝ :=
    (conditionalMeanResistance (rule.generation fine).network parameter /
      conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter) *
        finiteMean (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
          (rule.generation fine).network.conditionalCellWeight parameter true)) (fun cells =>
            electricalCell (rule.generation coarse).network configuration
              (fun edge => positiveNormalizedResistance (rule.generation fine).network parameter (cells edge)))

theorem generation_block_normalized_resistance_joint_observable_parent_mean
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (coarse fine : ℕ)
    (response : Configuration (rule.generation coarse).edges → ℝ → ℝ) :
    finiteMean ((rule.generation (coarse+fine+1)).network.conditionalCellWeight parameter true)
      (fun configuration => response (generationBlockCoarse rule coarse fine configuration)
        (normalizedConfigurationResistance (rule.generation (coarse+fine+1)).network parameter configuration)) =
      finiteMean ((rule.generation coarse).network.conditionalCellWeight parameter true) (fun outerConfiguration =>
        finiteMean (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
          (rule.generation fine).network.conditionalCellWeight parameter true)) (fun cells =>
            response outerConfiguration
              ((conditionalMeanResistance (rule.generation fine).network parameter /
                conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter) *
                  electricalCell (rule.generation coarse).network outerConfiguration
                    (fun edge => positiveNormalizedResistance (rule.generation fine).network parameter (cells edge))))) := by
  have meanPositive := generation_conditionalMeanResistance_positive rule classical parameter positive belowOne fixedPoint fine
  have law := generation_block_normalized_resistance_joint_observable rule classical parameter positive belowOne fixedPoint
    coarse fine (fun outerConfiguration value => response outerConfiguration
      ((conditionalMeanResistance (rule.generation fine).network parameter /
        conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter) * value))
  refine Eq.trans ?_ law
  unfold finiteMean
  apply Finset.sum_congr rfl
  intro configuration _
  congr 2
  unfold normalizedConfigurationResistance
  field_simp

theorem electricalBlockConditionalMean_eq_scaled_mean
    (rule : Rule) (parameter : ℝ) (coarse fine : ℕ)
    (configuration : Configuration (rule.generation coarse).edges) :
    electricalBlockConditionalMean rule parameter coarse fine configuration =
      finiteMean (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
        (rule.generation fine).network.conditionalCellWeight parameter true)) (fun cells =>
          (conditionalMeanResistance (rule.generation fine).network parameter /
            conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter) *
              electricalCell (rule.generation coarse).network configuration
                (fun edge => positiveNormalizedResistance (rule.generation fine).network parameter (cells edge))) :=
  (finiteMean_const_mul _ _ _).symm

theorem generation_block_electrical_residual_second_moment
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (coarse fine : ℕ) :
    finiteMean ((rule.generation (coarse+fine+1)).network.conditionalCellWeight parameter true)
      (fun configuration =>
        (normalizedConfigurationResistance (rule.generation (coarse+fine+1)).network parameter configuration -
          electricalBlockConditionalMean rule parameter coarse fine (generationBlockCoarse rule coarse fine configuration))^2) =
      (conditionalMeanResistance (rule.generation fine).network parameter /
        conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter)^2 *
          finiteMean ((rule.generation coarse).network.conditionalCellWeight parameter true) (fun outerConfiguration =>
            finiteVariance (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
              (rule.generation fine).network.conditionalCellWeight parameter true)) (fun cells =>
                electricalCell (rule.generation coarse).network outerConfiguration
                  (fun edge => positiveNormalizedResistance (rule.generation fine).network parameter (cells edge)))) := by
  have law := generation_block_normalized_resistance_joint_observable_parent_mean rule classical parameter positive belowOne fixedPoint
    coarse fine (fun configuration value => (value-electricalBlockConditionalMean rule parameter coarse fine configuration)^2)
  simp_rw [electricalBlockConditionalMean_eq_scaled_mean] at law
  change _ = finiteMean ((rule.generation coarse).network.conditionalCellWeight parameter true) (fun outerConfiguration =>
    IGSIII.Probability.finiteVariance (tupleWeight (fun _ : Fin (rule.generation coarse).edges =>
      (rule.generation fine).network.conditionalCellWeight parameter true)) (fun cells =>
        (conditionalMeanResistance (rule.generation fine).network parameter /
          conditionalMeanResistance (rule.generation (coarse+fine+1)).network parameter) *
            electricalCell (rule.generation coarse).network outerConfiguration
              (fun edge => positiveNormalizedResistance (rule.generation fine).network parameter (cells edge)))) at law
  simp_rw [electricalBlockConditionalMean_eq_scaled_mean]
  simp_rw [finiteVariance_scale] at law
  exact law.trans (finiteMean_const_mul _ _ _)

theorem generation_block_electrical_conditionalMean_second_moment
    (rule : Rule) (classical : rule.Classical) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (coarse fine : ℕ) :
    finiteMean ((rule.generation coarse).network.conditionalCellWeight parameter true)
      (fun configuration => (electricalBlockConditionalMean rule parameter coarse fine configuration)^2) ≤
      finiteMean ((rule.generation (coarse+fine+1)).network.conditionalCellWeight parameter true)
        (fun configuration => (normalizedConfigurationResistance (rule.generation (coarse+fine+1)).network parameter configuration)^2) := by
  have law := generation_block_normalized_resistance_joint_observable_parent_mean rule classical parameter positive belowOne fixedPoint
    coarse fine (fun _ value => value^2)
  apply le_trans _ law.symm.le
  apply finiteMean_mono _ ((rule.generation coarse).network.conditionalCellWeight_nonneg positive.le belowOne.le true)
  intro configuration
  rw [electricalBlockConditionalMean_eq_scaled_mean]
  exact finite_weighted_mean_sq_le _ _
    (tupleWeight_nonnegative _ (fun _ => (rule.generation fine).network.conditionalCellWeight_nonneg positive.le belowOne.le true))
    (tupleWeight_normalized _ (fun _ => (rule.generation fine).network.sum_conditionalCellWeight parameter
      (by rwa [rule.generation_fixed_point parameter fixedPoint])
      (by rwa [rule.generation_fixed_point parameter fixedPoint]) true))

end
end IGSIII34.Percolation
