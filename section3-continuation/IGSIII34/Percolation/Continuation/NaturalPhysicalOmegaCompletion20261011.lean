import IGSIII34.Percolation.Continuation.NaturalResistanceCompletion20261011
import IGSIII34.ResistanceLimit.ActualSkeletonLimit

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open IGSIII34.ResistanceLimit MeasureTheory Filter
open scoped Topology NNReal

/-- The physical endpoint of every constructed natural-resistance witness
is a genuine omega limit of the original unit-edge electrical orbit.
The original deterministic growth bounds are supplied by the same model. -/
theorem natural_physical_omega_witness_completion20261011
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint) :
    ∃ constant : ℝ, 0 < constant ∧
      (∀ depth, natural.growth ^ depth ≤
          (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
        (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * natural.growth ^ depth) ∧
      (natural.amplitude • natural.field) ∈ electricalOmegaSet rule p positive belowOne fixedPoint natural.growth ∧
      normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 natural.growth
        (natural.amplitude • natural.field) = natural.amplitude • natural.field := by
  obtain ⟨constant, growth, constantPositive, _, growthLower, _, growthBounds,
    field, fieldFixed, fieldPositive, fieldMeanOne, amplitude, amplitudeLower, membership, _, _⟩ :=
    exists_actual_electrical_fixed_ray_endpoint rule classical p positive belowOne fixedPoint
      (fun configuration => (network rule.network configuration).graph.dist rule.network.source rule.network.target)
      (fun _ _ => le_rfl)
  have growthAboveOne := (rule.network.interior_fixed_point_strictly_unstable
    p positive belowOne fixedPoint classical.scale).trans_le growthLower
  have growthPositive := zero_lt_one.trans growthAboveOne
  have amplitudePositive := zero_lt_one.trans_le amplitudeLower
  have endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth
      (amplitude • field) = amplitude • field := by
    rw [normalizedElectricalTransferLp_smul rule p positive belowOne fixedPoint 2 growth
      amplitude amplitudePositive.le, fieldFixed]
  have orbitLimit := electricalOrbitLp_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint
    constant growth growthPositive growthBounds (amplitude • field) endpointFixed membership
  have memberEquality (member : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
      (memberMembership : member ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
      member = amplitude • field := by
    obtain ⟨subsequence, increasing, limit⟩ := memberMembership.tendsto_subseq
    exact tendsto_nhds_unique limit (orbitLimit.comp increasing.tendsto_atTop)
  have fieldMoments : ∀ exponent : ℝ, Integrable (fun marks => (field marks)^exponent)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    apply electricalField_all_real_moments_of_omega_sandwich rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds field fieldPositive
      amplitude amplitude amplitudePositive amplitudePositive
    intro member memberMembership
    rw [memberEquality member memberMembership]
    exact ⟨le_rfl, le_rfl⟩
  have multiplier := (natural.eigenlawUnique (Real.toNNReal growth)
    (electricalFixedLaw rule p positive belowOne fixedPoint field)
    (electricalFixedLaw_positive_ae rule p positive belowOne fixedPoint field fieldPositive)
    (electricalFixedLaw_all_real_moments rule p positive belowOne fixedPoint field fieldPositive fieldMoments)
    (electricalFixedLaw_mean_one rule p positive belowOne fixedPoint field fieldPositive fieldMeanOne)
    (electricalFixedLaw_output_scaling rule p positive belowOne fixedPoint growth growthPositive field fieldPositive fieldFixed)).1
  have growthEquality : growth = natural.growth := by
    have equality := congrArg (fun number : ℝ≥0 => (number : ℝ)) multiplier
    simpa only [Real.coe_toNNReal _ growthPositive.le,
      Real.coe_toNNReal _ (zero_lt_one.trans natural.aboveOne).le] using equality
  rw [growthEquality] at growthBounds endpointFixed membership
  have rootConvergence := actual_electrical_field_limits_fixed_cluster rule classical p positive belowOne fixedPoint
    constant natural.growth constantPositive (zero_lt_one.trans natural.aboveOne) growthBounds
    (amplitude • field) endpointFixed membership
  have physicalEquality : amplitude • field = natural.amplitude • natural.field := by
    apply Lp.ext
    filter_upwards [rootConvergence, natural.almostSure, Lp.coeFn_smul natural.amplitude natural.field]
      with marks rawLimit naturalLimit scalar
    have equality := tendsto_nhds_unique (rawLimit []) (naturalLimit [])
    have nilShift : innovationTreeShift rule [] marks = marks := by
      funext coordinate
      simp only [innovationTreeShift, List.nil_append, Prod.eta]
    rw [scalar]
    simpa only [electricalField, nilShift, Pi.smul_apply, smul_eq_mul] using equality
  refine ⟨constant, constantPositive, growthBounds, ?_, ?_⟩
  · rwa [← physicalEquality]
  · rwa [← physicalEquality]

end
end IGSIII34.Percolation
