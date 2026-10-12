import IGSIII.Chemical.SubstitutionPaths.GrowthCompactFamily

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped ENNReal

/-- The actual quasi-multiplicative chemical growth improves the block mean
ratio beyond the reliability-derivative lower bound. -/
theorem generation_block_mean_ratio_chemical_growth
    (rule : Rule) (p constant growth : ℝ)
    (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (coarse fine : ℕ) :
    conditionedDistanceMean (rule.generation fine).network p /
      conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p ≤
        constant⁻¹ / growth ^ (coarse + 1) := by
  have parentPositive : 0 < conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p :=
    (pow_pos growthPositive (coarse + fine + 2)).trans_le (meanBounds (coarse + fine + 2)).1
  apply (div_le_div_iff₀ parentPositive (pow_pos growthPositive (coarse + 1))).mpr
  calc
    conditionedDistanceMean (rule.generation fine).network p * growth ^ (coarse + 1) ≤
        (constant⁻¹ * growth ^ (fine + 1)) * growth ^ (coarse + 1) :=
      mul_le_mul_of_nonneg_right (meanBounds (fine + 1)).2 (pow_pos growthPositive _).le
    _ = constant⁻¹ * growth ^ (coarse + fine + 2) := by
      rw [mul_assoc, ← pow_add]
      congr 2
      omega
    _ ≤ constant⁻¹ * conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p :=
      mul_le_mul_of_nonneg_left (meanBounds (coarse + fine + 2)).1 (inv_pos.mpr constantPositive).le

/-- Literal chemical-growth geometric rate for the finite normalised residual. -/
theorem generation_block_residual_variance_chemical_growth
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (coarse fine : ℕ) {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth, normalizedDistanceMoment (rule.generation depth).network p 2 ≤ secondMoment)
    (inverseMomentBound : finiteMean ((rule.generation fine).network.conditionalCellWeight p true)
      (fun configuration => (normalizedDistance (rule.generation fine).network p configuration)⁻¹ ^ power) ≤ inverseMoment) :
    finiteMean ((rule.generation (coarse + fine + 1)).network.conditionalCellWeight p true)
      (fun configuration =>
        (normalizedDistance (rule.generation (coarse + fine + 1)).network p configuration -
          blockConditionalMean rule p coarse fine (generationBlockCoarse rule coarse fine configuration)) ^ 2) ≤
      (constant⁻¹ * (2 * secondMoment * Real.sqrt secondMoment * inverseMoment ^ (1 / power))) *
        (((rule.edges : ℝ) ^ (1 / power)) / growth) ^ (coarse + 1) := by
  have bound := generation_block_residual_variance_bound rule classical p positive belowOne fixedPoint
    coarse fine powerAtLeastTwo secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative
    secondMomentBound inverseMomentBound
  refine bound.trans ((mul_le_mul_of_nonneg_left
    (generation_block_mean_ratio_chemical_growth rule p constant growth constantPositive growthPositive meanBounds coarse fine)
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) secondMomentNonnegative) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) inverseMomentNonnegative) _))).trans_eq ?_)
  rw [rule.generation_edges, Nat.cast_pow,
    Real.mul_rpow (pow_nonneg (Nat.cast_nonneg _) _) inverseMomentNonnegative,
    ← Real.rpow_pow_comm (Nat.cast_nonneg _), div_pow]
  ring

/-- The actual common-tree L2 residual has the chemical-growth rate. -/
theorem marked_prefix_residual_variance_chemical_growth
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (address : List (Fin rule.edges)) (coarse fine : ℕ) {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth, normalizedDistanceMoment (rule.generation depth).network p 2 ≤ secondMoment)
    (inverseMomentBound : finiteMean ((rule.generation fine).network.conditionalCellWeight p true)
      (fun configuration => (normalizedDistance (rule.generation fine).network p configuration)⁻¹ ^ power) ≤ inverseMoment) :
    ‖markedObservableLp rule p positive belowOne fixedPoint (coarse + fine + 1) address true
        (normalizedDistance (rule.generation (coarse + fine + 1)).network p) -
      markedObservableLp rule p positive belowOne fixedPoint coarse address true
        (blockConditionalMean rule p coarse fine)‖ ^ 2 ≤
      (constant⁻¹ * (2 * secondMoment * Real.sqrt secondMoment * inverseMoment ^ (1 / power))) *
        (((rule.edges : ℝ) ^ (1 / power)) / growth) ^ (coarse + 1) := by
  rw [marked_prefix_residual_norm_sq]
  exact generation_block_residual_variance_chemical_growth rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive meanBounds coarse fine powerAtLeastTwo
    secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative secondMomentBound inverseMomentBound

/-- The same exact rate for the actual growth-scaled terminal distance, with
the corresponding growth-scaled conditional mean. -/
theorem marked_growth_scaled_prefix_residual_variance
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (address : List (Fin rule.edges)) (coarse fine : ℕ) {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (secondMoment inverseMoment : ℝ) (secondMomentNonnegative : 0 ≤ secondMoment)
    (inverseMomentNonnegative : 0 ≤ inverseMoment)
    (secondMomentBound : ∀ depth, normalizedDistanceMoment (rule.generation depth).network p 2 ≤ secondMoment)
    (inverseMomentBound : finiteMean ((rule.generation fine).network.conditionalCellWeight p true)
      (fun configuration => (normalizedDistance (rule.generation fine).network p configuration)⁻¹ ^ power) ≤ inverseMoment) :
    ‖markedObservableLp rule p positive belowOne fixedPoint (coarse + fine + 1) address true
        (growthScaledDistance rule growth (coarse + fine + 1)) -
      (conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p / growth ^ (coarse + fine + 2)) •
        markedObservableLp rule p positive belowOne fixedPoint coarse address true
          (blockConditionalMean rule p coarse fine)‖ ^ 2 ≤
      (constant⁻¹ ^ 3 * (2 * secondMoment * Real.sqrt secondMoment * inverseMoment ^ (1 / power))) *
        (((rule.edges : ℝ) ^ (1 / power)) / growth) ^ (coarse + 1) := by
  have meanPositive : 0 < conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p :=
    (pow_pos growthPositive (coarse + fine + 2)).trans_le (meanBounds (coarse + fine + 2)).1
  have observableIdentity :
      markedObservableLp rule p positive belowOne fixedPoint (coarse + fine + 1) address true
        (growthScaledDistance rule growth (coarse + fine + 1)) =
      (conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p / growth ^ (coarse + fine + 2)) •
        markedObservableLp rule p positive belowOne fixedPoint (coarse + fine + 1) address true
          (normalizedDistance (rule.generation (coarse + fine + 1)).network p) := by
    rw [← markedObservableLp_scale]
    congr 1
    funext configuration
    exact growthScaledDistance_eq_mean_ratio rule p growth growthPositive (coarse + fine + 1) meanPositive configuration
  rw [observableIdentity, ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have scalarNonnegative : 0 ≤ conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p / growth ^ (coarse + fine + 2) :=
    (div_pos meanPositive (pow_pos growthPositive _)).le
  have scalarBound : conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p / growth ^ (coarse + fine + 2) ≤ constant⁻¹ :=
    (div_le_iff₀ (pow_pos growthPositive _)).mpr (meanBounds (coarse + fine + 2)).2
  have squaredBound := pow_le_pow_left₀ scalarNonnegative scalarBound 2
  have residualBound := marked_prefix_residual_variance_chemical_growth rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive meanBounds address coarse fine powerAtLeastTwo
    secondMoment inverseMoment secondMomentNonnegative inverseMomentNonnegative secondMomentBound inverseMomentBound
  calc
    _ ≤ constant⁻¹ ^ 2 *
        ‖markedObservableLp rule p positive belowOne fixedPoint (coarse + fine + 1) address true
          (normalizedDistance (rule.generation (coarse + fine + 1)).network p) -
          markedObservableLp rule p positive belowOne fixedPoint coarse address true
            (blockConditionalMean rule p coarse fine)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right squaredBound (sq_nonneg _)
    _ ≤ constant⁻¹ ^ 2 *
        ((constant⁻¹ * (2 * secondMoment * Real.sqrt secondMoment * inverseMoment ^ (1 / power))) *
          (((rule.edges : ℝ) ^ (1 / power)) / growth) ^ (coarse + 1)) :=
      mul_le_mul_of_nonneg_left residualBound (sq_nonneg _)
    _ = _ := by ring


/-- Every moment premise in the growth-rate estimate is discharged from the
original percolation model. The growth certificate supplies only its proved
mean comparison, rather than a residual or conditional-variance conclusion. -/
theorem exists_marked_growth_scaled_prefix_residual_rate
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ (address : List (Fin rule.edges)) (coarse fine : ℕ),
      ‖markedObservableLp rule p positive belowOne fixedPoint (coarse + fine + 1) address true
          (growthScaledDistance rule growth (coarse + fine + 1)) -
        (conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p / growth ^ (coarse + fine + 2)) •
          markedObservableLp rule p positive belowOne fixedPoint coarse address true
            (blockConditionalMean rule p coarse fine)‖ ^ 2 ≤
        bound * (((rule.edges : ℝ) ^ (1 / power)) / growth) ^ (coarse + 1) := by
  obtain ⟨secondMoment, secondBound⟩ := exists_uniform_generation_positive_moment rule classical.simple p
    positive belowOne fixedPoint classical.scale 2
  obtain ⟨inverseMoment, inverseBound⟩ := exists_uniform_generation_real_inverse_moment rule classical.simple p
    positive belowOne fixedPoint classical.scale (exponent := power) (by linarith)
  refine ⟨max 1 (constant⁻¹ ^ 3 * (2 * max 1 secondMoment * Real.sqrt (max 1 secondMoment) *
    (max 1 inverseMoment) ^ (1 / power))),
    zero_lt_one.trans_le (le_max_left _ _), fun address coarse fine => ?_⟩
  have bound := marked_growth_scaled_prefix_residual_variance rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive meanBounds address coarse fine powerAtLeastTwo
    (max 1 secondMoment) (max 1 inverseMoment)
    (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_left _ _))
    (fun depth => (secondBound depth).trans (le_max_right _ _)) (by
      have comparison := (inverseBound fine).trans (le_max_right 1 inverseMoment)
      simpa only [finiteMean, Real.rpow_neg_eq_inv_rpow] using comparison)
  exact bound.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
    (pow_nonneg (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) growthPositive.le) _))

/-- Original-model-only construction of a contracting literal chemical-growth
variance rate, with no moment, growth certificate, or target bound supplied. -/
theorem exists_actual_chemical_growth_prefix_variance_rate
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ constant growth power bound : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      (∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
        manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) ∧
      2 ≤ power ∧ (rule.edges : ℝ) ^ (1 / power) < growth ∧ 0 < bound ∧
      ∀ (address : List (Fin rule.edges)) (coarse fine : ℕ),
        ‖markedObservableLp rule p positive belowOne fixedPoint (coarse + fine + 1) address true
            (growthScaledDistance rule growth (coarse + fine + 1)) -
          (conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p / growth ^ (coarse + fine + 2)) •
            markedObservableLp rule p positive belowOne fixedPoint coarse address true
              (blockConditionalMean rule p coarse fine)‖ ^ 2 ≤
          bound * (((rule.edges : ℝ) ^ (1 / power)) / growth) ^ (coarse + 1) := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds⟩ :=
    exists_actual_chemical_growth rule classical p positive belowOne fixedPoint
  have fullDistanceAboveOne : (1 : ℝ) < rule.network.fullGraph.dist rule.network.source rule.network.target := by
    exact_mod_cast classical.scale
  have growthAboveOne : 1 < growth := fullDistanceAboveOne.trans_le growthLower
  obtain ⟨power, powerAtLeastTwo, contracts⟩ := exists_inverse_power_contracting (rule.edges : ℝ) growth growthAboveOne
  obtain ⟨bound, boundPositive, valid⟩ := exists_marked_growth_scaled_prefix_residual_rate
    rule classical p positive belowOne fixedPoint constant growth constantPositive
    (zero_lt_one.trans growthAboveOne) meanBounds powerAtLeastTwo
  exact ⟨constant, growth, power, bound, constantPositive, constantAtMostOne, growthLower, growthUpper,
    meanBounds, powerAtLeastTwo, contracts, boundPositive, valid⟩

end
end IGSIII.Chemical.Substitution
