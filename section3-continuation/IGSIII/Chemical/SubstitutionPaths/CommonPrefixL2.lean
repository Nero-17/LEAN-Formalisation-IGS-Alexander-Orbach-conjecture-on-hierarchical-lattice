import IGSIII.Chemical.SubstitutionPaths.CommonPrefix
import IGSIII.Chemical.SubstitutionPaths.GenerationVariance
import Universality.Percolation.InfiniteObservables
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Actual normalized distances and their fixed-prefix approximations in
L2 of the common independent crossing/noncrossing innovation space. -/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped BigOperators ENNReal

theorem independentInnovationLaw_marked_observable (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (response : Configuration (rule.generation depth).edges → ℝ) :
    (∫ marks, response (markedGenerationConfiguration rule marks depth address opened)
      ∂independentInnovationLaw rule p positive lessOne fixedPoint) =
        finiteMean ((rule.generation depth).network.conditionalCellWeight p opened) response := by
  have historyMeasurable : Measurable (fun marks => Rule.ConfigurationHistory.ofFine rule depth
      (markedGenerationConfiguration rule marks depth address opened)) :=
    (measurable_of_countable _).comp (markedGenerationConfiguration_measurable rule depth address opened)
  calc
    _ = ∫ history, response (Rule.ConfigurationHistory.latest rule depth history)
        ∂Rule.ConfigurationHistory.law rule p positive lessOne fixedPoint opened depth := by
      rw [← independentInnovationLaw_history_marginal rule p positive lessOne fixedPoint depth address opened,
        integral_map_of_stronglyMeasurable historyMeasurable (measurable_of_countable _).stronglyMeasurable]
      simp only [Rule.ConfigurationHistory.latest_ofFine]
    _ = _ := by
      rw [Rule.ConfigurationHistory.integral_law,
        Rule.ConfigurationHistory.joint_observable_law rule p positive lessOne fixedPoint]
      simp only [Rule.ConfigurationHistory.latest_ofFine, finiteMean]

theorem marked_observable_memLp (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (response : Configuration (rule.generation depth).edges → ℝ) (order : ℝ≥0∞) :
    MemLp (fun marks => response (markedGenerationConfiguration rule marks depth address opened)) order
      (independentInnovationLaw rule p positive lessOne fixedPoint) := by
  apply MemLp.of_bound
    (((measurable_of_countable response).comp
      (markedGenerationConfiguration_measurable rule depth address opened)).aestronglyMeasurable)
    (∑ configuration, ‖response configuration‖)
  exact Filter.Eventually.of_forall (fun marks => Finset.single_le_sum
    (fun configuration _ => norm_nonneg (response configuration)) (Finset.mem_univ _))

noncomputable def markedObservableLp (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (response : Configuration (rule.generation depth).edges → ℝ) :
    Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint) :=
  (marked_observable_memLp rule p positive lessOne fixedPoint depth address opened response 2).toLp
    (fun marks => response (markedGenerationConfiguration rule marks depth address opened))

theorem markedObservableLp_ae (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (response : Configuration (rule.generation depth).edges → ℝ) :
    markedObservableLp rule p positive lessOne fixedPoint depth address opened response =ᵐ[
      independentInnovationLaw rule p positive lessOne fixedPoint]
        (fun marks => response (markedGenerationConfiguration rule marks depth address opened)) :=
  MemLp.coeFn_toLp _

theorem lp_norm_sq_eq_integral {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (value : Lp ℝ 2 measure) :
    ‖value‖ ^ 2 = ∫ sample, value sample ^ 2 ∂measure := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem markedObservableLp_norm_sq (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool)
    (response : Configuration (rule.generation depth).edges → ℝ) :
    ‖markedObservableLp rule p positive lessOne fixedPoint depth address opened response‖ ^ 2 =
      finiteMean ((rule.generation depth).network.conditionalCellWeight p opened)
        (fun configuration => response configuration ^ 2) := by
  rw [lp_norm_sq_eq_integral]
  refine (integral_congr_ae ?_).trans
    (independentInnovationLaw_marked_observable rule p positive lessOne fixedPoint depth address opened _)
  exact (markedObservableLp_ae rule p positive lessOne fixedPoint depth address opened response).mono
    (fun marks equality => congrArg (fun value : ℝ => value ^ 2) equality)

theorem marked_prefix_residual_norm_sq (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (address : List (Fin rule.edges)) (coarse fine : ℕ) :
    ‖markedObservableLp rule p positive lessOne fixedPoint (coarse + fine + 1) address true
        (normalizedDistance (rule.generation (coarse + fine + 1)).network p) -
      markedObservableLp rule p positive lessOne fixedPoint coarse address true
        (blockConditionalMean rule p coarse fine)‖ ^ 2 =
      finiteMean ((rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true)
        (fun configuration =>
          (normalizedDistance (rule.generation (coarse + fine + 1)).network p configuration -
            blockConditionalMean rule p coarse fine (generationBlockCoarse rule coarse fine configuration)) ^ 2) := by
  rw [lp_norm_sq_eq_integral]
  refine (integral_congr_ae ?_).trans
    (independentInnovationLaw_marked_observable rule p positive lessOne fixedPoint
      (coarse + fine + 1) address true _)
  filter_upwards [Lp.coeFn_sub
      (markedObservableLp rule p positive lessOne fixedPoint (coarse + fine + 1) address true
        (normalizedDistance (rule.generation (coarse + fine + 1)).network p))
      (markedObservableLp rule p positive lessOne fixedPoint coarse address true (blockConditionalMean rule p coarse fine)),
    markedObservableLp_ae rule p positive lessOne fixedPoint (coarse + fine + 1) address true
      (normalizedDistance (rule.generation (coarse + fine + 1)).network p),
    markedObservableLp_ae rule p positive lessOne fixedPoint coarse address true (blockConditionalMean rule p coarse fine),
    marked_generationBlockCoarse_eq_ae rule p positive lessOne fixedPoint]
      with marks subtraction distanceEquality meanEquality coarseEquality
  rw [subtraction, Pi.sub_apply, distanceEquality, meanEquality, coarseEquality address true coarse fine]

theorem marked_prefix_conditionalMean_norm_sq_le (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (address : List (Fin rule.edges)) (coarse fine : ℕ) :
    ‖markedObservableLp rule p positive lessOne fixedPoint coarse address true
      (blockConditionalMean rule p coarse fine)‖ ^ 2 ≤
        normalizedDistanceMoment (rule.generation (coarse + fine + 1)).network p 2 := by
  rw [markedObservableLp_norm_sq]
  exact generation_block_conditionalMean_second_moment rule classical p positive lessOne fixedPoint coarse fine

theorem marked_prefix_residual_variance_geometric (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (address : List (Fin rule.edges)) (coarse fine : ℕ)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth, normalizedDistanceMoment (rule.generation depth).network p 2 ≤ secondMoment)
    (inverseMomentBound : finiteMean ((rule.generation fine).network.conditionalCellWeight p true)
      (fun configuration => (normalizedDistance (rule.generation fine).network p configuration)⁻¹ ^ power) ≤ inverseMoment) :
    ‖markedObservableLp rule p positive lessOne fixedPoint (coarse + fine + 1) address true
        (normalizedDistance (rule.generation (coarse + fine + 1)).network p) -
      markedObservableLp rule p positive lessOne fixedPoint coarse address true
        (blockConditionalMean rule p coarse fine)‖ ^ 2 ≤
      (2 * secondMoment * Real.sqrt secondMoment * inverseMoment ^ (1 / power)) *
        (((rule.edges : ℝ) ^ (1 / power)) / deriv rule.network.reliability p) ^ (coarse + 1) := by
  rw [marked_prefix_residual_norm_sq]
  exact generation_block_residual_variance_geometric rule classical p positive lessOne fixedPoint coarse fine
    powerAtLeastTwo secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative
    secondMomentBound inverseMomentBound

end IGSIII.Chemical.Substitution
