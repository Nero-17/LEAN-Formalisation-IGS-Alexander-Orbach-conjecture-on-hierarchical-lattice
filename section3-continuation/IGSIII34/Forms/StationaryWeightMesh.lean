import IGSIII34.ResistanceLimit.ActualCompactness
import IGSIII34.Percolation.Continuation.ElectricalAddressEnvelope

/-! Actual stationary generation edge weights vanish uniformly. This supplies
the trace-endpoint mesh after the elementary resistance-versus-edge bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped Topology ENNReal

theorem ae_stationary_generation_weight_mesh_fixed_cluster
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthGreaterThanOne : 1 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (endpoint : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (eta : ℝ) (etaPositive : 0 < eta) (etaBelowOne : eta < 1) (productGreaterThanOne : 1 < growth * eta) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ threshold : ℕ, ∀ depth, threshold ≤ depth + 1 → ∀ edge,
        stationaryGenerationResistance rule
          (fun address => electricalField rule p positive belowOne fixedPoint endpoint address marks)
          growth depth [] edge ≤ eta ^ (depth + 1) := by
  have growthPositive := zero_lt_one.trans growthGreaterThanOne
  have productPositive := mul_pos growthPositive etaPositive
  have largePower := (tendsto_pow_atTop_atTop_of_one_lt productGreaterThanOne).eventually
    (eventually_gt_atTop (rule.edges : ℝ))
  obtain ⟨power, powerPositive, momentGrowth⟩ :=
    ((eventually_gt_atTop (0 : ℕ)).and largePower).exists
  obtain ⟨envelope, bound, boundFinite, envelopeProperties, bounds⟩ :=
    electricalIteration_exists_uniform_address_envelope_fixed_cluster rule classicalRule p positive belowOne
      fixedPoint constant growth constantPositive growthPositive growthBounds endpoint endpointFixed membership power powerPositive
  have decay : (rule.edges : ℝ≥0∞) * (ENNReal.ofReal (growth * eta))⁻¹ ^ power < 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos productPositive,
      ← ENNReal.ofReal_pow (inv_nonneg.mpr productPositive.le),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg rule.edges)]
    apply ENNReal.ofReal_lt_one.mpr
    rw [inv_pow, ← div_eq_mul_inv]
    exact (div_lt_one (pow_pos productPositive power)).mpr momentGrowth
  have descendants := IGSIII.Geometry.ae_descendant_envelope_exponential rule.edges power powerPositive
    (fun address (_ : Bool) => envelope address)
    (fun address _ => (envelopeProperties address).1.aestronglyMeasurable) bound
    (ENNReal.ofReal (growth * eta)) boundFinite (ENNReal.ofReal_ne_zero_iff.mpr productPositive)
    ENNReal.ofReal_ne_top (fun address _ => (envelopeProperties address).2.2.2) decay
  filter_upwards [descendants, bounds,
    actual_electrical_field_limits_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds endpoint endpointFixed membership]
    with marks descendants bounds fieldLimits
  obtain ⟨threshold, small⟩ := eventually_atTop.mp descendants
  refine ⟨threshold, ?_⟩
  intro depth after edge
  have fieldBelow : electricalField rule p positive belowOne fixedPoint endpoint
      (generationEdgeAddress rule depth edge) marks ≤ envelope (generationEdgeAddress rule depth edge) marks :=
    le_of_tendsto (fieldLimits _) (Filter.Eventually.of_forall (fun index => bounds _ index))
  have addressAfter : threshold ≤ (generationEdgeAddress rule depth edge).length := by
    simpa only [generationEdgeAddress_length] using after
  have envelopeSmall := small (generationEdgeAddress rule depth edge).length addressAfter
    (generationEdgeAddress rule depth edge).get false
  rw [List.ofFn_get] at envelopeSmall
  have absBound : |envelope (generationEdgeAddress rule depth edge) marks| <
      (growth * eta) ^ (depth + 1) := by
    apply (ENNReal.ofReal_lt_ofReal_iff (pow_pos productPositive (depth + 1))).mp
    simpa only [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow productPositive.le,
      generationEdgeAddress_length] using envelopeSmall
  have fieldBound := fieldBelow.trans ((le_abs_self _).trans absBound.le)
  have scaled := mul_le_mul_of_nonneg_left fieldBound (pow_pos (inv_pos.mpr growthPositive) (depth + 1)).le
  have cancellation : growth⁻¹ ^ (depth + 1) * (growth * eta) ^ (depth + 1) = eta ^ (depth + 1) := by
    rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ growthPositive.ne', one_pow, one_mul]
  rw [cancellation] at scaled
  simpa only [stationaryGenerationResistance, List.nil_append] using scaled

end
end IGSIII34.Forms
