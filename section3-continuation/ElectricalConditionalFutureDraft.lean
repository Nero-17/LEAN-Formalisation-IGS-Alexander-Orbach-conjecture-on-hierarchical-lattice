import IGSIII34.Percolation.ElectricalCoefficientConditional
import IGSIII34.Percolation.ElectricalFixedEnvelope
import IGSIII34.Percolation.ElectricalFutureMean

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal _root_.Topology

variable (rule : Rule) (classical : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
  (constantPositive : 0 < constant) (growthPositive : 0 < growth)
  (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
    (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)

local notation "μ" => independentInnovationLaw rule p positive belowOne fixedPoint
local notation "W" => electricalOrbitLp rule p positive belowOne fixedPoint growth
local notation "T" => normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth
local notation "F" => coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)

include classical constantPositive growthPositive growthBounds in
theorem electricalOrbit_future_conditional_bounds
    (endpoint : Lp ℝ 2 μ) (endpointFixed : T endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) (block : ℕ) :
    (∀ᵐ marks ∂μ, ∀ᶠ depth : ℕ in atTop,
      μ[fun marks => max (W (depth+1+block) marks-endpoint marks) 0 | F (depth+1)] marks ≤
        electricalComparisonCoefficient μ (W block) endpoint*(endpoint marks+1)) ∧
    (∀ᵐ marks ∂μ, ∀ᶠ depth : ℕ in atTop,
      μ[fun marks => max (endpoint marks-W (depth+1+block) marks) 0 | F (depth+1)] marks ≤
        electricalComparisonCoefficient μ endpoint (W block)*
          (constant⁻¹*((∫ marks, (endpoint marks)⁻¹ ∂μ)*endpoint marks+1))) := by
  have endpointPositive := electricalOmega_ae_positive rule classical p positive belowOne fixedPoint growth
    growthPositive (fun depth => (growthBounds depth).1) endpoint membership
  have orbitPositive := electricalOrbitLp_ae_positive rule classical p positive belowOne fixedPoint constant growth growthPositive growthBounds
  obtain ⟨orbitBound, orbitMoments⟩ := electricalOrbit_uniform_integrable_inverse_natural_moment
    rule classical p positive belowOne fixedPoint growth growthPositive (fun depth => (growthBounds depth).1) 4
  obtain ⟨omegaBound, omegaMoments⟩ := electricalOmega_uniform_integrable_inverse_natural_moment
    rule classical p positive belowOne fixedPoint growth growthPositive (fun depth => (growthBounds depth).1) 4
  obtain ⟨inverseBound, inverseMoments⟩ := electricalOmega_uniform_integrable_inverse_natural_moment
    rule classical p positive belowOne fixedPoint growth growthPositive (fun depth => (growthBounds depth).1) 1
  have inverseIntegrable : Integrable (fun marks => (endpoint marks)⁻¹) μ := by
    simpa only [pow_one] using (inverseMoments endpoint membership).1
  have forwardComparisons (depth : ℕ) : ∀ᵐ marks ∂μ,
      μ[fun marks => max (W (depth+1+block) marks-endpoint marks) 0 | F (depth+1)] marks ≤
        electricalComparisonCoefficient μ (W block) endpoint*μ[⇑endpoint | F (depth+1)] marks := by
    have comparison := normalized_electrical_conditional_comparison_coefficient rule p positive belowOne fixedPoint growth growthPositive.le
      (W block) endpoint (orbitPositive block) endpointPositive (omegaMoments endpoint membership).1 depth
    rwa [Function.iterate_fixed endpointFixed, electricalOrbitLp_iterate rule p positive belowOne fixedPoint growth] at comparison
  have reverseComparisons (depth : ℕ) : ∀ᵐ marks ∂μ,
      μ[fun marks => max (endpoint marks-W (depth+1+block) marks) 0 | F (depth+1)] marks ≤
        electricalComparisonCoefficient μ endpoint (W block)*μ[⇑(W (depth+1+block)) | F (depth+1)] marks := by
    have comparison := normalized_electrical_conditional_comparison_coefficient rule p positive belowOne fixedPoint growth growthPositive.le
      endpoint (W block) endpointPositive (orbitPositive block) (orbitMoments block).1 depth
    rwa [Function.iterate_fixed endpointFixed, electricalOrbitLp_iterate rule p positive belowOne fixedPoint growth] at comparison
  have futureUpper (depth : ℕ) : ∀ᵐ marks ∂μ,
      μ[⇑(W (depth+1+block)) | F (depth+1)] marks ≤ (∫ marks, W block marks ∂μ)*W (depth+1) marks := by
    have upper := normalized_electrical_boundary_conditional_mean_upper rule p positive belowOne fixedPoint growth growthPositive.le
      (W block) (orbitPositive block) (∫ marks, W block marks ∂μ)
      (integral_nonneg_of_ae ((orbitPositive block).mono (fun _ inequality => inequality.le))) rfl depth
    rw [electricalOrbitLp_iterate rule p positive belowOne fixedPoint growth] at upper
    filter_upwards [upper, electricalOrbitLp_coe_ae_unit_generation rule p positive belowOne fixedPoint growth growthPositive.le depth]
      with marks upper equality
    rwa [← equality] at upper
  constructor
  · have convergence := coordinatePrefixFiltration_condExp_tendsto
      (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) μ (⇑endpoint)
      (Lp.stronglyMeasurable endpoint) ((Lp.memLp endpoint).integrable (by norm_num))
    filter_upwards [convergence, ae_all_iff.mpr forwardComparisons] with marks limit comparisons
    have eventual := (limit.comp (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds (lt_add_one (endpoint marks)))
    exact eventual.mono (fun depth bound => (comparisons depth).trans
      (mul_le_mul_of_nonneg_left bound.le (electricalComparisonCoefficient_nonnegative μ (W block) endpoint endpointPositive)))
  · have envelope := electricalOrbit_eventually_below_arbitrary_fixed_envelope rule p positive belowOne fixedPoint growth growthPositive.le
      endpoint endpointPositive endpointFixed inverseIntegrable
    filter_upwards [envelope, ae_all_iff.mpr reverseComparisons, ae_all_iff.mpr futureUpper,
      ae_all_iff.mpr orbitPositive] with marks eventual comparisons uppers positives
    have shifted := (tendsto_add_atTop_nat 1).eventually eventual
    apply shifted.mono
    intro depth bound
    have conditionalBound : μ[⇑(W (depth+1+block)) | F (depth+1)] marks ≤
        constant⁻¹*((∫ marks, (endpoint marks)⁻¹ ∂μ)*endpoint marks+1) :=
      (uppers depth).trans ((mul_le_mul_of_nonneg_right
        (electricalOrbitLp_mean_atMost rule classical p positive belowOne fixedPoint constant growth growthPositive growthBounds block)
        (positives (depth+1)).le).trans (mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr constantPositive.le)))
    exact (comparisons depth).trans (mul_le_mul_of_nonneg_left conditionalBound
      (electricalComparisonCoefficient_nonnegative μ endpoint (W block) (orbitPositive block)))

end
end IGSIII34.Percolation

