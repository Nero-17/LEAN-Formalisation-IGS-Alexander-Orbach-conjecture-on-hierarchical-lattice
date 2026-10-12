import IGSIII34.Percolation.Continuation.EigenlawCompletion
import IGSIII34.Percolation.Continuation.ElectricalLpAllOrder
import IGSIII34.Percolation.Continuation.ElectricalSupremum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace IGSIII34.Percolation
noncomputable section

open MeasureTheory Universality Universality.FiniteNetwork Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal _root_.Topology

/-- One actual innovation-tree witness for the natural electrical multiplier,
stationary field, physical amplitudes and their complete moment conclusions. -/
structure NaturalResistanceCompletion
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) where
  growth : ℝ
  aboveOne : 1 < growth
  field : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint)
  fieldPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
    0 < field marks
  fieldMeanOne : (∫ marks, field marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1
  fieldFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth field = field
  fieldMoments : ∀ exponent : ℝ, Integrable (fun marks => (field marks)^exponent)
    (independentInnovationLaw rule p positive belowOne fixedPoint)
  fieldStationary : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
    ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint field (address ++ [edge]) marks) =
        growth * electricalField rule p positive belowOne fixedPoint field address marks
  amplitude : ℝ
  amplitudeLower : 1 ≤ amplitude
  almostSure : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
    ∀ address : List (Fin rule.edges),
      Tendsto (fun depth => growth⁻¹^depth * electricalIteration rule marks depth address)
        atTop (𝓝 (amplitude * electricalField rule p positive belowOne fixedPoint field address marks))
  errorMoments : ∀ address : List (Fin rule.edges), ∀ exponent : ℝ, 0 < exponent →
    Tendsto (fun depth => ∫ marks,
      |growth⁻¹^depth * electricalIteration rule marks depth address -
        amplitude * electricalField rule p positive belowOne fixedPoint field address marks|^exponent
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) atTop (𝓝 0)
  lpConvergence : ∀ address : List (Fin rule.edges), ∀ exponent : ℝ, 0 < exponent →
    Tendsto (fun depth => eLpNorm (fun marks =>
      growth⁻¹^depth * electricalIteration rule marks depth address -
        amplitude * electricalField rule p positive belowOne fixedPoint field address marks)
      (ENNReal.ofReal exponent) (independentInnovationLaw rule p positive belowOne fixedPoint))
      atTop (𝓝 0)
  realMoments : ∀ address : List (Fin rule.edges), ∀ exponent : ℝ,
    Tendsto (fun depth => ∫ marks,
      (growth⁻¹^depth * electricalIteration rule marks depth address)^exponent
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) atTop
      (𝓝 (∫ marks, (amplitude * electricalField rule p positive belowOne fixedPoint field address marks)^exponent
        ∂independentInnovationLaw rule p positive belowOne fixedPoint))
  supremumMoments : ∀ address : List (Fin rule.edges), ∀ exponent : ℝ, 0 < exponent →
    (∫⁻ marks, (⨆ depth : ℕ,
      ENNReal.ofReal (growth⁻¹^depth * electricalIteration rule marks depth address))^exponent
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≠ ∞
  eigenlawUnique : ∀ (otherGrowth : ℝ≥0) (otherLaw : ProbabilityMeasure ℝ≥0),
    (∀ᵐ value ∂(otherLaw : Measure ℝ≥0), 0 < value) →
    (∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value : ℝ)^exponent) (otherLaw : Measure ℝ≥0)) →
    (∫ value : ℝ≥0, (value : ℝ) ∂(otherLaw : Measure ℝ≥0)) = 1 →
    electricalOutputLaw rule p positive belowOne fixedPoint otherLaw = scaledProbabilityLaw otherGrowth otherLaw →
      otherGrowth = Real.toNNReal growth ∧
        otherLaw = electricalFixedLaw rule p positive belowOne fixedPoint field

theorem exists_natural_resistance_completion
    (rule : Rule) (classical : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    Nonempty (NaturalResistanceCompletion rule p positive belowOne fixedPoint) := by
  obtain ⟨constant, growth, constantPositive, _, growthLower, _, growthBounds,
    field, fieldFixed, fieldPositive, fieldMeanOne, amplitude, amplitudeLower, membership, _, _⟩ :=
    exists_actual_electrical_fixed_ray_endpoint rule classical p positive belowOne fixedPoint
      (fun configuration => (network rule.network configuration).graph.dist
        rule.network.source rule.network.target) (fun _ _ => le_rfl)
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
  have scalarEquality (address : List (Fin rule.edges)) :
      electricalField rule p positive belowOne fixedPoint (amplitude • field) address =ᵐ[
        independentInnovationLaw rule p positive belowOne fixedPoint]
      fun marks => amplitude * electricalField rule p positive belowOne fixedPoint field address marks := by
    have shifted := (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae
      (Lp.coeFn_smul amplitude field)
    filter_upwards [shifted] with marks equality
    simpa only [electricalField, Pi.smul_apply, smul_eq_mul] using equality
  have convergence := electricalOrbitLp_tendsto_ae_fixed_cluster rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive growthBounds (amplitude • field) endpointFixed membership
  have rootLimit : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      Tendsto (fun depth => growth⁻¹^depth * electricalIteration rule marks depth []) atTop
        (𝓝 (amplitude * field marks)) := by
    filter_upwards [convergence,
      ae_all_iff.mpr (electricalOrbitLp_coe_ae_actual rule p positive belowOne fixedPoint growth growthPositive.le),
      Lp.coeFn_smul amplitude field] with marks limit equalities scalar
    simpa only [equalities, scalar, Pi.smul_apply, smul_eq_mul] using limit
  refine ⟨{
    growth := growth
    aboveOne := growthAboveOne
    field := field
    fieldPositive := fieldPositive
    fieldMeanOne := fieldMeanOne
    fieldFixed := fieldFixed
    fieldMoments := fieldMoments
    fieldStationary := electricalField_stationary_of_fixed rule p positive belowOne fixedPoint
      growth growthPositive field fieldPositive fieldFixed
    amplitude := amplitude
    amplitudeLower := amplitudeLower
    almostSure := ?_
    errorMoments := ?_
    lpConvergence := ?_
    realMoments := ?_
    supremumMoments := electricalIteration_supremum_real_moment_finite_fixed_cluster rule classical
      p positive belowOne fixedPoint constant growth constantPositive growthPositive growthBounds
      (amplitude • field) endpointFixed membership
    eigenlawUnique := ?_
  }⟩
  · apply ae_all_iff.mpr
    intro address
    have shifted := (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae rootLimit
    simpa only [electricalIteration_shift, List.append_nil, electricalField] using shifted
  · intro address exponent exponentPositive
    apply (electricalIteration_absolute_error_moment_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds (amplitude • field) endpointFixed membership
      address exponent exponentPositive).congr'
    apply Eventually.of_forall
    intro depth
    exact integral_congr_ae ((scalarEquality address).mono (fun marks equality => by
      dsimp only at equality ⊢
      rw [equality]))
  · intro address exponent exponentPositive
    apply (electricalIteration_eLpNorm_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds (amplitude • field) endpointFixed membership
      address exponent exponentPositive).congr'
    apply Eventually.of_forall
    intro depth
    exact eLpNorm_congr_ae ((scalarEquality address).mono (fun marks equality => by
      dsimp only at equality ⊢
      rw [equality]))
  · intro address exponent
    have limit := electricalIteration_real_moment_tendsto_fixed_cluster rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive growthBounds (amplitude • field) endpointFixed membership address exponent
    have equality : (∫ marks,
        (electricalField rule p positive belowOne fixedPoint (amplitude • field) address marks)^exponent
          ∂independentInnovationLaw rule p positive belowOne fixedPoint) =
        ∫ marks, (amplitude * electricalField rule p positive belowOne fixedPoint field address marks)^exponent
          ∂independentInnovationLaw rule p positive belowOne fixedPoint :=
      integral_congr_ae ((scalarEquality address).mono (fun marks equality => by
        dsimp only at equality ⊢
        rw [equality]))
    rwa [equality] at limit
  · intro otherGrowth otherLaw otherPositive otherMoments otherMean otherEigenlaw
    have fieldLawPositive := electricalFixedLaw_positive_ae rule p positive belowOne fixedPoint field fieldPositive
    have fieldLawMoments := electricalFixedLaw_all_real_moments rule p positive belowOne fixedPoint field fieldPositive fieldMoments
    have fieldLawMean := electricalFixedLaw_mean_one rule p positive belowOne fixedPoint field fieldPositive fieldMeanOne
    have fieldLawEigen := electricalFixedLaw_output_scaling rule p positive belowOne fixedPoint growth growthPositive
      field fieldPositive fieldFixed
    have lawsEqual := electrical_positive_mean_one_eigenlaw_unique_actual_completion rule classical
      p positive belowOne fixedPoint otherLaw (electricalFixedLaw rule p positive belowOne fixedPoint field)
      otherPositive fieldLawPositive otherMoments fieldLawMoments otherMean fieldLawMean otherGrowth
      (Real.toNNReal growth) otherEigenlaw fieldLawEigen
    exact ⟨electrical_mean_one_eigenlaw_multiplier_unique_completion rule p positive belowOne fixedPoint
      (electricalFixedLaw rule p positive belowOne fixedPoint field) fieldLawMean otherGrowth (Real.toNNReal growth)
      (lawsEqual ▸ otherEigenlaw) fieldLawEigen, lawsEqual⟩

end
end IGSIII34.Percolation
