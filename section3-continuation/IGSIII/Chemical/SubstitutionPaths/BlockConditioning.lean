import IGSIII.Chemical.SubstitutionPaths.ConditionalVariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Conditional means and conditional residuals obtained from the actual
generation block decomposition. The test-function identity identifies the
finite conditional expectation, rather than postulating a variance bound. -/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped BigOperators

theorem generation_block_distance_eq_cellMinPlus (rule : Rule) (classical : rule.Classical)
    (coarse fine : ℕ) (configuration : Configuration (rule.generation (coarse + fine + 1)).edges) :
    (((rule.generation (coarse + fine + 1)).network.openGraph configuration).dist
      (rule.generation (coarse + fine + 1)).network.source
      (rule.generation (coarse + fine + 1)).network.target : ℝ) =
        cellMinPlus (rule.generation coarse).network (rule.generation fine).network
          (generationBlockCoarse rule coarse fine configuration)
          (generationBlockCells rule coarse fine configuration) := by
  have identity := networkEquivalence_terminal_distance_all
    (rule.generationBlockDecomposition coarse fine) configuration
  have cellsIdentity : substitutionConfigurationEquiv (generationBlockCells rule coarse fine configuration) =
      (rule.generationBlockDecomposition coarse fine).configuration configuration := by
    simp [generationBlockCells, generationBlockCellsEquiv]
  rw [← identity, ← cellsIdentity]
  exact substitute_distance_eq_cellMinPlus _ _ (classical.generation coarse).simple _

noncomputable def blockConditionalMean (rule : Rule) (p : ℝ) (coarse fine : ℕ)
    (outerConfiguration : Configuration (rule.generation coarse).edges) : ℝ :=
  finiteMean (tupleWeight (fun edge => (rule.generation fine).network.conditionalCellWeight p
    (outerConfiguration edge))) (fun cells =>
      cellMinPlus (rule.generation coarse).network (rule.generation fine).network outerConfiguration cells /
        conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p)

theorem generation_block_coarse_observable (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (coarse fine : ℕ)
    (response : Configuration (rule.generation coarse).edges → ℝ) :
    finiteMean ((rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true)
      (fun configuration => response (generationBlockCoarse rule coarse fine configuration)) =
        finiteMean ((rule.generation coarse).network.conditionalCellWeight p true) response := by
  have law := actual_generation_block_observable rule p positive lessOne fixedPoint coarse fine
    (fun outerConfiguration _ => response outerConfiguration)
  change _ = finiteMean ((rule.generation coarse).network.conditionalCellWeight p true)
    (fun outerConfiguration => finiteMean
      (tupleWeight (fun edge => (rule.generation fine).network.conditionalCellWeight p
        (outerConfiguration edge))) (fun _ => response outerConfiguration)) at law
  simp_rw [finiteMean_const _ (tupleWeight_normalized _ (fun _ =>
    (rule.generation fine).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) _))] at law
  exact law

theorem generation_block_conditionalMean_test (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (coarse fine : ℕ)
    (test : Configuration (rule.generation coarse).edges → ℝ) :
    finiteMean ((rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true)
      (fun configuration => test (generationBlockCoarse rule coarse fine configuration) *
        (normalizedDistance (rule.generation (coarse + fine + 1)).network p configuration -
          blockConditionalMean rule p coarse fine (generationBlockCoarse rule coarse fine configuration))) = 0 := by
  have law := actual_generation_block_observable rule p positive lessOne fixedPoint coarse fine
    (fun outerConfiguration cells => test outerConfiguration *
      (cellMinPlus (rule.generation coarse).network (rule.generation fine).network outerConfiguration cells /
        conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p -
          blockConditionalMean rule p coarse fine outerConfiguration))
  simp_rw [← generation_block_distance_eq_cellMinPlus rule classical] at law
  change _ = _ at law
  refine law.trans ?_
  apply Finset.sum_eq_zero
  intro outerConfiguration _
  have normalized := tupleWeight_normalized
    (fun edge => (rule.generation fine).network.conditionalCellWeight p (outerConfiguration edge))
    (fun _ => (rule.generation fine).network.sum_conditionalCellWeight p
      (by rwa [rule.generation_fixed_point p fixedPoint])
      (by rwa [rule.generation_fixed_point p fixedPoint]) _)
  have constant := finiteMean_const _ normalized (blockConditionalMean rule p coarse fine outerConfiguration)
  change _ * finiteMean _ _ = 0
  simp only [finiteMean, tupleWeight] at constant ⊢
  simp only [mul_sub, Finset.sum_sub_distrib, mul_left_comm _ (test outerConfiguration),
    ← Finset.mul_sum]
  rw [constant]
  simp [blockConditionalMean, finiteMean, tupleWeight]

theorem generation_block_residual_second_moment (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (coarse fine : ℕ) :
    finiteMean ((rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true)
      (fun configuration =>
        (normalizedDistance (rule.generation (coarse + fine + 1)).network p configuration -
          blockConditionalMean rule p coarse fine (generationBlockCoarse rule coarse fine configuration)) ^ 2) =
      finiteMean ((rule.generation coarse).network.conditionalCellWeight p true)
        (fun outerConfiguration => finiteVariance
          (tupleWeight (fun edge => (rule.generation fine).network.conditionalCellWeight p (outerConfiguration edge)))
          (fun cells => cellMinPlus (rule.generation coarse).network (rule.generation fine).network
            outerConfiguration cells / conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p)) := by
  have law := actual_generation_block_observable rule p positive lessOne fixedPoint coarse fine
    (fun outerConfiguration cells =>
      (cellMinPlus (rule.generation coarse).network (rule.generation fine).network outerConfiguration cells /
        conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p -
          blockConditionalMean rule p coarse fine outerConfiguration) ^ 2)
  simp_rw [← generation_block_distance_eq_cellMinPlus rule classical] at law
  exact law

theorem generation_block_conditionalMean_second_moment (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (coarse fine : ℕ) :
    finiteMean ((rule.generation coarse).network.conditionalCellWeight p true)
      (fun outerConfiguration => blockConditionalMean rule p coarse fine outerConfiguration ^ 2) ≤
        normalizedDistanceMoment (rule.generation (coarse + fine + 1)).network p 2 := by
  have law := actual_generation_block_observable rule p positive lessOne fixedPoint coarse fine
    (fun outerConfiguration cells =>
      (cellMinPlus (rule.generation coarse).network (rule.generation fine).network outerConfiguration cells /
        conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p) ^ 2)
  simp_rw [← generation_block_distance_eq_cellMinPlus rule classical] at law
  calc
    _ ≤ finiteMean ((rule.generation coarse).network.conditionalCellWeight p true)
        (fun outerConfiguration => finiteMean
          (tupleWeight (fun edge => (rule.generation fine).network.conditionalCellWeight p (outerConfiguration edge)))
          (fun cells =>
            (cellMinPlus (rule.generation coarse).network (rule.generation fine).network outerConfiguration cells /
              conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p) ^ 2)) := by
      unfold finiteMean
      apply Finset.sum_le_sum
      intro outerConfiguration _
      apply mul_le_mul_of_nonneg_left _
        ((rule.generation coarse).network.conditionalCellWeight_nonneg positive.le lessOne.le true outerConfiguration)
      exact finite_weighted_mean_sq_le _ _
        (tupleWeight_nonnegative _ (fun edge configuration =>
          (rule.generation fine).network.conditionalCellWeight_nonneg positive.le lessOne.le _ configuration))
        (tupleWeight_normalized _ (fun _ =>
          (rule.generation fine).network.sum_conditionalCellWeight p
            (by rwa [rule.generation_fixed_point p fixedPoint])
            (by rwa [rule.generation_fixed_point p fixedPoint]) _))
    _ = _ := law.symm

end IGSIII.Chemical.Substitution
