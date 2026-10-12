import IGSIII.Chemical.SubstitutionPaths.PrefixConditionalVariance20261011
import IGSIII.Chemical.SubstitutionPaths.ChemicalGrowthVariance20261011
import IGSIII.Chemical.SmallBall.ChemicalOrbitConvergence

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped ENNReal Topology

/-- Literal chemical-rate estimate for conditional expectation on the actual
raw first k innovation generations, including k=0 and n=k. -/
theorem exists_raw_prefix_variance_rate_of_mean_bounds20261011
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ prefixDepth depth : ℕ, prefixDepth ≤ depth →
      ‖rawPrefixResidual20261011 rule p positive belowOne fixedPoint prefixDepth
        (chemicalOrbit rule p positive belowOne fixedPoint growth depth)‖ ^ 2 ≤
      bound * (((rule.edges : ℝ) ^ (1 / power)) / growth) ^ prefixDepth := by
  obtain ⟨finiteBound, finiteBoundPositive, finiteEstimate⟩ :=
    exists_marked_growth_scaled_prefix_residual_rate20261011 rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive meanBounds powerAtLeastTwo
  obtain ⟨normBound, normBoundPositive, normEstimate⟩ :=
    (chemicalOrbit_compact_closure rule classical p positive belowOne fixedPoint constant growth growthPositive meanBounds).isBounded.exists_pos_norm_le
  refine ⟨max finiteBound (normBound ^ 2), finiteBoundPositive.trans_le (le_max_left _ _), ?_⟩
  intro prefixDepth depth prefixBound
  cases prefixDepth with
  | zero =>
    have contraction := rawPrefixResidual_le_approximation20261011 rule p positive belowOne fixedPoint 0
      (chemicalOrbit rule p positive belowOne fixedPoint growth depth) 0
      (aestronglyMeasurable_zero.congr
        (Lp.coeFn_zero ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)).symm)
    simp only [sub_zero] at contraction
    have orbitBound := normEstimate (chemicalOrbit rule p positive belowOne fixedPoint growth depth)
      (subset_closure ⟨depth, rfl⟩)
    simpa only [pow_zero, mul_one] using
      (pow_le_pow_left₀ (norm_nonneg _) (contraction.trans orbitBound) 2).trans (le_max_right finiteBound (normBound ^ 2))
  | succ coarse =>
    by_cases equalDepth : depth = coarse + 1
    · subst depth
      rw [chemicalOrbit_tail_eq_actual rule classical p positive belowOne fixedPoint growth growthPositive.le,
        rawPrefixResidual_zero_of_measurable20261011 rule p positive belowOne fixedPoint (coarse + 1) _
          (markedObservableLp_rawPrefix_measurable20261011 rule p positive belowOne fixedPoint coarse
            (growthScaledDistance rule growth coarse)), norm_zero, zero_pow (by decide : 2 ≠ 0)]
      exact mul_nonneg (le_trans finiteBoundPositive.le (le_max_left _ _))
        (pow_nonneg (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) growthPositive.le) _)
    · obtain ⟨fine, depthIdentity⟩ : ∃ fine : ℕ, depth = coarse + fine + 2 := ⟨depth - coarse - 2, by omega⟩
      rw [depthIdentity, show coarse + fine + 2 = (coarse + fine + 1) + 1 by omega,
        chemicalOrbit_tail_eq_actual rule classical p positive belowOne fixedPoint growth growthPositive.le]
      have approximationMeasurable :=
        ((markedObservableLp_rawPrefix_measurable20261011 rule p positive belowOne fixedPoint coarse
          (blockConditionalMean rule p coarse fine)).const_smul
          (conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p / growth ^ (coarse + fine + 2))).congr
          (Lp.coeFn_smul
            (conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p / growth ^ (coarse + fine + 2))
            (markedObservableLp rule p positive belowOne fixedPoint coarse [] true (blockConditionalMean rule p coarse fine))).symm
      have projectionBound := rawPrefixResidual_le_approximation20261011 rule p positive belowOne fixedPoint (coarse + 1)
        (markedObservableLp rule p positive belowOne fixedPoint (coarse + fine + 1) [] true
          (growthScaledDistance rule growth (coarse + fine + 1)))
        ((conditionedDistanceMean (rule.generation (coarse + fine + 1)).network p / growth ^ (coarse + fine + 2)) •
          markedObservableLp rule p positive belowOne fixedPoint coarse [] true (blockConditionalMean rule p coarse fine))
        approximationMeasurable
      exact ((pow_le_pow_left₀ (norm_nonneg _) projectionBound 2).trans (finiteEstimate [] coarse fine)).trans
        (mul_le_mul_of_nonneg_right (le_max_left finiteBound (normBound ^ 2))
          (pow_nonneg (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) growthPositive.le) _))

/-- Both displayed chemical conditional-variance rates, constructed from the
actual model alone. The fixed field is the same positive mean-one original-tree
field and the same deterministic chemical growth used for the distance orbit. -/
theorem exists_actual_raw_prefix_conditional_variance_rate20261011
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ constant growth power bound : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      (∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
        manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) ∧
      2 ≤ power ∧ (rule.edges : ℝ) ^ (1 / power) < growth ∧ 0 < bound ∧
      ∃ value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
        normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth value = value ∧
        (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) ∧
        (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
        (∀ prefixDepth depth : ℕ, prefixDepth ≤ depth →
          ‖rawPrefixResidual20261011 rule p positive belowOne fixedPoint prefixDepth
            (chemicalOrbit rule p positive belowOne fixedPoint growth depth)‖ ^ 2 ≤
          bound * (((rule.edges : ℝ) ^ (1 / power)) / growth) ^ prefixDepth) ∧
        (∀ prefixDepth : ℕ,
          ‖rawPrefixResidual20261011 rule p positive belowOne fixedPoint prefixDepth value‖ ^ 2 ≤
          bound * (((rule.edges : ℝ) ^ (1 / power)) / growth) ^ prefixDepth) := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds,
    value, valueFixed, valuePositive, valueMeanOne, lower, upper, lowerPositive, upperPositive, comparison,
    amplitude, amplitudeAtLeastOne, endpoint, dominates, convergence⟩ :=
      exists_actual_chemical_orbit_convergence rule classical p positive belowOne fixedPoint
  have growthAboveOne : 1 < growth :=
    (by exact_mod_cast classical.scale : (1 : ℝ) < rule.network.fullGraph.dist rule.network.source rule.network.target).trans_le growthLower
  have growthPositive := zero_lt_one.trans growthAboveOne
  obtain ⟨power, powerAtLeastTwo, contracts⟩ := exists_inverse_power_contracting (rule.edges : ℝ) growth growthAboveOne
  obtain ⟨bound, boundPositive, finiteEstimate⟩ := exists_raw_prefix_variance_rate_of_mean_bounds20261011
    rule classical p positive belowOne fixedPoint constant growth constantPositive growthPositive meanBounds powerAtLeastTwo
  refine ⟨constant, growth, power, bound, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds,
    powerAtLeastTwo, contracts, boundPositive, value, valueFixed, valuePositive, valueMeanOne, finiteEstimate, ?_⟩
  intro prefixDepth
  obtain ⟨subsequence, increasing, subsequenceConvergence⟩ := endpoint.tendsto_subseq
  apply rawPrefixResidual_bound_of_scalar_limit20261011 rule p positive belowOne fixedPoint prefixDepth
    (bound * (((rule.edges : ℝ) ^ (1 / power)) / growth) ^ prefixDepth) amplitude amplitudeAtLeastOne
    (chemicalOrbit rule p positive belowOne fixedPoint growth ∘ subsequence) value subsequenceConvergence
  filter_upwards [increasing.tendsto_atTop.eventually (eventually_ge_atTop prefixDepth)] with index beyond
  exact finiteEstimate prefixDepth (subsequence index) beyond

end
end IGSIII.Chemical.Substitution
