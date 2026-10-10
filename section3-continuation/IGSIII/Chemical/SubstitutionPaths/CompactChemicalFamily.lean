import IGSIII.Chemical.SubstitutionPaths.CommonPrefixL2
import IGSIII.Probability.FiniteFactorCompact
import IGSIII.Chemical.SmallBall.FiniteDepthSmallBall

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped Topology ENNReal

noncomputable def markedNormalizedDistanceFamily (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges)) :
    Set (Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint)) :=
  Set.range (fun depth => markedObservableLp rule p positive lessOne fixedPoint depth address true
    (normalizedDistance (rule.generation depth).network p))

noncomputable def markedPrefixApproximationSet (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges))
    (coarse : ℕ) (secondMoment : ℝ) :
    Set (Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint)) :=
  factorBall (independentInnovationLaw rule p positive lessOne fixedPoint) 2
      (fun marks => markedGenerationConfiguration rule marks coarse address true)
      (markedGenerationConfiguration_measurable rule coarse address true) (Real.sqrt secondMoment) ∪
    Set.range (fun depth : Fin (coarse + 1) =>
      markedObservableLp rule p positive lessOne fixedPoint depth address true
        (normalizedDistance (rule.generation depth).network p))

theorem markedPrefixApproximationSet_compact (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges))
    (coarse : ℕ) (secondMoment : ℝ) :
    IsCompact (markedPrefixApproximationSet rule p positive lessOne fixedPoint address coarse secondMoment) :=
  (factorBall_compact _ _ _ _ _).union (Set.finite_range _).isCompact

theorem marked_prefix_conditionalMean_mem_compact (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges))
    (coarse fine : ℕ) (secondMoment : ℝ)
    (secondMomentBound : normalizedDistanceMoment (rule.generation (coarse + fine + 1)).network p 2 ≤ secondMoment) :
    markedObservableLp rule p positive lessOne fixedPoint coarse address true
      (blockConditionalMean rule p coarse fine) ∈
        markedPrefixApproximationSet rule p positive lessOne fixedPoint address coarse secondMoment := by
  apply Or.inl
  apply mem_factorBall_of_coe_ae _ _ _ _ _ (blockConditionalMean rule p coarse fine)
  · exact markedObservableLp_ae rule p positive lessOne fixedPoint coarse address true _
  · exact Real.le_sqrt_of_sq_le
      ((marked_prefix_conditionalMean_norm_sq_le rule classical p positive lessOne fixedPoint address coarse fine).trans
        secondMomentBound)

theorem markedNormalizedDistanceFamily_compact_closure_of_inverse_moment
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges))
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (powerContracts : (rule.edges : ℝ) ^ (1 / power) < deriv rule.network.reliability p)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth, normalizedDistanceMoment (rule.generation depth).network p 2 ≤ secondMoment)
    (inverseMomentBound : ∀ depth,
      finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
        (fun configuration => (normalizedDistance (rule.generation depth).network p configuration)⁻¹ ^ power) ≤ inverseMoment) :
    IsCompact (closure (markedNormalizedDistanceFamily rule p positive lessOne fixedPoint address)) := by
  have derivativePositive : 0 < deriv rule.network.reliability p :=
    zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable p positive lessOne fixedPoint classical.scale)
  have ratioNonnegative : 0 ≤ (rule.edges : ℝ) ^ (1 / power) / deriv rule.network.reliability p :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) derivativePositive.le
  have ratioLessOne : (rule.edges : ℝ) ^ (1 / power) / deriv rule.network.reliability p < 1 :=
    (div_lt_one derivativePositive).mpr powerContracts
  apply compact_closure_of_compact_approximations
    (markedNormalizedDistanceFamily rule p positive lessOne fixedPoint address)
    (fun coarse => markedPrefixApproximationSet rule p positive lessOne fixedPoint address coarse secondMoment)
    (fun coarse => Real.sqrt
      ((2 * secondMoment * Real.sqrt secondMoment * inverseMoment ^ (1 / power)) *
        ((rule.edges : ℝ) ^ (1 / power) / deriv rule.network.reliability p) ^ (coarse + 1)))
    (fun coarse => markedPrefixApproximationSet_compact rule p positive lessOne fixedPoint address coarse secondMoment)
  · have geometric := tendsto_pow_atTop_nhds_zero_of_lt_one ratioNonnegative ratioLessOne
    have shifted := geometric.mul_const ((rule.edges : ℝ) ^ (1 / power) / deriv rule.network.reliability p)
    have scaled := shifted.const_mul (2 * secondMoment * Real.sqrt secondMoment * inverseMoment ^ (1 / power))
    simpa only [Function.comp_def, pow_succ, mul_zero, zero_mul, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp scaled
  · intro coarse _ membership
    obtain ⟨depth, rfl⟩ := membership
    by_cases early : depth ≤ coarse
    · refine ⟨markedObservableLp rule p positive lessOne fixedPoint depth address true
          (normalizedDistance (rule.generation depth).network p), Or.inr ?_, ?_⟩
      · exact ⟨⟨depth, by omega⟩, rfl⟩
      · rw [dist_self]
        exact Real.sqrt_nonneg _
    · obtain ⟨fine, rfl⟩ : ∃ fine, depth = coarse + fine + 1 := ⟨depth - coarse - 1, by omega⟩
      refine ⟨markedObservableLp rule p positive lessOne fixedPoint coarse address true
        (blockConditionalMean rule p coarse fine),
        marked_prefix_conditionalMean_mem_compact rule classical p positive lessOne fixedPoint address
          coarse fine secondMoment (secondMomentBound _), ?_⟩
      rw [dist_eq_norm]
      exact Real.le_sqrt_of_sq_le (marked_prefix_residual_variance_geometric rule classical p positive lessOne fixedPoint
        address coarse fine powerAtLeastTwo secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative
        secondMomentBound (inverseMomentBound fine))

theorem exists_inverse_power_contracting (base : ℝ)
    (growth : ℝ) (growthAboveOne : 1 < growth) :
    ∃ power : ℝ, 2 ≤ power ∧ base ^ (1 / power) < growth := by
  by_cases zeroBase : base = 0
  · refine ⟨2, le_rfl, ?_⟩
    simp only [zeroBase]
    rw [Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0)]
    exact zero_lt_one.trans growthAboveOne
  · have convergence : Tendsto (fun power : ℝ => base ^ (1 / power)) atTop (𝓝 1) := by
      simpa only [Function.comp_def, one_div, Real.rpow_zero] using
        (Real.continuousAt_const_rpow zeroBase).tendsto.comp tendsto_inv_atTop_zero
    have small := (tendsto_order.mp convergence).2 growth growthAboveOne
    obtain ⟨power, large, contract⟩ := ((eventually_ge_atTop (2 : ℝ)).and small).exists
    exact ⟨power, large, contract⟩

theorem markedNormalizedDistanceFamily_compact_closure_of_all_inverse_moments
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges))
    (inverseMoments : ∀ power : ℝ, 2 ≤ power → ∃ bound : ℝ, ∀ depth,
      finiteMean ((rule.generation depth).network.conditionalCellWeight p true)
        (fun configuration => (normalizedDistance (rule.generation depth).network p configuration)⁻¹ ^ power) ≤ bound) :
    IsCompact (closure (markedNormalizedDistanceFamily rule p positive lessOne fixedPoint address)) := by
  obtain ⟨power, powerAtLeastTwo, powerContracts⟩ := exists_inverse_power_contracting (rule.edges : ℝ)
    (deriv rule.network.reliability p)
    (rule.network.interior_fixed_point_strictly_unstable p positive lessOne fixedPoint classical.scale)
  obtain ⟨inverseMoment, inverseBound⟩ := inverseMoments power powerAtLeastTwo
  obtain ⟨secondMoment, secondBound⟩ := exists_uniform_generation_positive_moment rule classical.simple p
    positive lessOne fixedPoint classical.scale 2
  apply markedNormalizedDistanceFamily_compact_closure_of_inverse_moment rule classical p positive lessOne fixedPoint address
    powerAtLeastTwo powerContracts secondMoment inverseMoment
  · exact (normalizedDistanceMoment_nonnegative _ positive.le lessOne.le
      (le_trans zero_le_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
        (by rwa [rule.generation_fixed_point p fixedPoint])
        (by rwa [rule.generation_fixed_point p fixedPoint]))) 2).trans (secondBound 0)
  · apply le_trans _ (inverseBound 0)
    unfold finiteMean
    apply Finset.sum_nonneg
    intro configuration _
    exact mul_nonneg (rule.network.conditionalCellWeight_nonneg positive.le lessOne.le true configuration)
      (Real.rpow_nonneg (inv_nonneg.mpr (normalizedDistance_nonnegative _
        (le_trans zero_le_one (conditionedDistanceMean_atLeastOne _ positive.le lessOne.le
          (by rwa [rule.generation_fixed_point p fixedPoint])
          (by rwa [rule.generation_fixed_point p fixedPoint]))) configuration)) _)
  · exact secondBound
  · exact inverseBound

theorem markedNormalizedDistanceFamily_compact_closure
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (address : List (Fin rule.edges)) :
    IsCompact (closure (markedNormalizedDistanceFamily rule p positive lessOne fixedPoint address)) := by
  apply markedNormalizedDistanceFamily_compact_closure_of_all_inverse_moments rule classical p positive lessOne fixedPoint address
  intro power powerAtLeastTwo
  obtain ⟨bound, valid⟩ := exists_uniform_generation_real_inverse_moment rule classical.simple p positive lessOne fixedPoint
    classical.scale (exponent := power) (by linarith)
  refine ⟨bound, fun depth => ?_⟩
  simpa only [finiteMean, Real.rpow_neg_eq_inv_rpow] using valid depth

end IGSIII.Chemical.Substitution
