import IGSIII34.Percolation.Continuation.ElectricalSupremum

set_option autoImplicit false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped ENNReal

variable (rule : Rule) (classical : rule.Classical)
  (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
  (constantPositive : 0 < constant) (growthPositive : 0 < growth)
  (growthBounds : ∀ depth, growth^depth ≤ (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
    (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹*growth^depth)

local notation "μ" => independentInnovationLaw rule p positive belowOne fixedPoint

include classical constantPositive growthPositive growthBounds in
theorem electricalIteration_exists_uniform_address_envelope_fixed_cluster
    (endpoint : Lp ℝ 2 μ)
    (endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (power : ℕ) (powerPositive : 0 < power) :
    ∃ envelope : List (Fin rule.edges) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∃ bound : ℝ≥0∞, bound ≠ ∞ ∧
      (∀ address, Measurable (envelope address) ∧ MemLp (envelope address) power μ ∧
        (∀ marks, 0 ≤ envelope address marks) ∧ eLpNorm (envelope address) power μ ≤ bound) ∧
      ∀ᵐ marks ∂μ, ∀ address depth,
        growth⁻¹^depth*electricalIteration rule marks depth address ≤ envelope address marks := by
  obtain ⟨rootEnvelope, measurable, memLp, nonnegative, bounds⟩ :=
    electricalOrbit_exists_memLp_uniform_envelope_fixed_cluster rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds endpoint endpointFixed membership
      (max power 2) (le_max_right _ _)
  have smallerMemLp : MemLp rootEnvelope power μ :=
    memLp.mono_exponent (by exact_mod_cast le_max_left power 2)
  have rootBounds : ∀ᵐ marks ∂μ, ∀ depth,
      growth⁻¹^depth*electricalIteration rule marks depth [] ≤ rootEnvelope marks := by
    filter_upwards [bounds,
      ae_all_iff.mpr (electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthPositive.le)]
      with marks bounds equalities
    intro depth
    rw [← equalities depth]
    exact bounds depth
  refine ⟨fun address => rootEnvelope ∘ innovationTreeShift rule address,
    eLpNorm rootEnvelope power μ, smallerMemLp.eLpNorm_ne_top, ?_, ?_⟩
  · intro address
    have preserving := innovationTreeShift_preserving rule p positive belowOne fixedPoint address
    refine ⟨measurable.comp preserving.measurable, smallerMemLp.comp_measurePreserving preserving,
      fun marks => nonnegative _, ?_⟩
    exact (eLpNorm_comp_measurePreserving smallerMemLp.aestronglyMeasurable preserving).le
  · apply ae_all_iff.mpr
    intro address
    have shifted := (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae rootBounds
    simpa only [Function.comp_apply, electricalIteration_shift, List.append_nil] using shifted

end
end IGSIII34.Percolation
