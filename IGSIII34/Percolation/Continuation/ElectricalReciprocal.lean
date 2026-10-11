import IGSIII34.Percolation.ElectricalSandwich

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open IGSIII34.Resistance.FiniteNetwork
open scoped ENNReal

theorem independent_conditional_electrical_inverse_upper
    {Sample History Boundary : Type*} [MeasurableSpace Sample] [MeasurableSpace History]
    [MeasurableSpace Boundary] [StandardBorelSpace Boundary] [Nonempty Boundary]
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (history : Sample → History) (boundary : Sample → Boundary)
    (historyMeasurable : Measurable history) (boundaryMeasurable : Measurable boundary)
    (independent : IndepFun history boundary measure)
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (configuration : History → Configuration edges) (configurationMeasurable : Measurable configuration)
    (input : Boundary → Fin edges → ℝ) (inputMeasurable : Measurable input)
    (positive : ∀ sample edge, 0 < input sample edge)
    (inverseIntegrable : ∀ edge, Integrable (fun sample => (input sample edge)⁻¹) (measure.map boundary))
    (inverseMean : ℝ) (inverseMeanPositive : 0 < inverseMean)
    (commonInverseMean : ∀ edge, (∫ sample, (input sample edge)⁻¹ ∂measure.map boundary) = inverseMean) :
    ∀ᵐ sample ∂measure,
      measure[fun sample => (electricalCell network (configuration (history sample)) (input (boundary sample)))⁻¹ |
        (inferInstance : MeasurableSpace History).comap history] sample ≤
      inverseMean / unitConfigurationResistance network (configuration (history sample)) := by
  letI : IsProbabilityMeasure (measure.map boundary) := Measure.isProbabilityMeasure_map boundaryMeasurable.aemeasurable
  have actualInverseIntegrable (edge : Fin edges) : Integrable (fun sample => (input (boundary sample) edge)⁻¹) measure :=
    (integrable_map_measure (((measurable_pi_apply edge).comp inputMeasurable).inv).aestronglyMeasurable
      boundaryMeasurable.aemeasurable).mp (inverseIntegrable edge)
  have responseMeasurable : Measurable (fun data : History × Boundary =>
      (electricalCell network (configuration data.1) (input data.2))⁻¹) :=
    (electricalCell_measurable network _ (configurationMeasurable.comp measurable_fst) _
      (inputMeasurable.comp measurable_snd) (fun data edge => (positive data.2 edge).le)).inv
  have responseIntegrable : Integrable (fun sample => (electricalCell network
      (configuration (history sample)) (input (boundary sample)))⁻¹) measure :=
    electricalCell_random_inverse_integrable measure network _ (configurationMeasurable.comp historyMeasurable)
      _ (inputMeasurable.comp boundaryMeasurable) (fun sample edge => positive (boundary sample) edge) actualInverseIntegrable
  have conditional := independent_pair_condExp_eq_integral measure history boundary historyMeasurable boundaryMeasurable
    independent _ responseMeasurable.stronglyMeasurable responseIntegrable
  filter_upwards [conditional] with sample equality
  rw [equality]
  by_cases crossing : network.crosses (configuration (history sample)) = true
  · exact (IGSIII34.Percolation.network network (configuration (history sample))).reciprocalResistance_integral_upper_bound
      (measure.map boundary) (connected_of_crosses network _ crossing)
      (fun sample edge => input sample edge.val)
      (measurable_pi_lambda _ (fun edge => (measurable_pi_apply edge.val).comp inputMeasurable))
      (fun sample edge => positive sample edge.val) (fun edge => inverseIntegrable edge.val)
      inverseMeanPositive (fun edge => commonInverseMean edge.val)
  · simp only [unitConfigurationResistance, electricalCell_eq_zero_of_not_crosses network _ crossing,
      inv_zero, div_zero, integral_zero, le_refl]

theorem actual_electrical_boundary_conditional_inverse_upper (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (inverseIntegrable : Integrable (fun marks => (value marks)⁻¹) (independentInnovationLaw rule p positive belowOne fixedPoint))
    (inverseMean : ℝ) (inverseMeanPositive : 0 < inverseMean)
    (inverseMeanEquality : (∫ marks, (value marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint) = inverseMean)
    (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      (independentInnovationLaw rule p positive belowOne fixedPoint)[fun marks =>
        (electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
          (fun leaf => positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)))⁻¹ |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks ≤
        inverseMean / unitConfigurationResistance (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true) := by
  have representativeEquality := positiveRepresentative_ae_eq _ valuePositive
  have representativeMeasurable := positiveRepresentative_measurable (Lp.stronglyMeasurable value).measurable
  have representativeIntegrable : Integrable (positiveRepresentative value) (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    ((Lp.memLp value).integrable (by norm_num)).congr representativeEquality.symm
  have inverseEquality : (fun marks => (positiveRepresentative value marks)⁻¹) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint] (fun marks => (value marks)⁻¹) := by
    filter_upwards [representativeEquality] with marks equality
    rw [equality]
  have inverseRepresentativeIntegrable := inverseIntegrable.congr inverseEquality.symm
  have boundaryMeasurable : Measurable (fun marks (leaf : Fin (rule.generation depth).edges) =>
      innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks) :=
    measurable_pi_lambda _ (fun leaf => innovationTreeShift_measurable rule (generationEdgeAddress rule depth leaf))
  have historyMeasurable : Measurable (fun (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1}) =>
      marks coordinate.val) := measurable_pi_lambda _ (fun coordinate => measurable_pi_apply coordinate.val)
  have inputMeasurable : Measurable (fun children : Fin (rule.generation depth).edges →
      ((List (Fin rule.edges) × Bool) → Configuration rule.edges) => fun leaf => positiveRepresentative value (children leaf)) :=
    measurable_pi_lambda _ (fun leaf => representativeMeasurable.comp (measurable_pi_apply leaf))
  have inputIntegrable (leaf : Fin (rule.generation depth).edges) :
      Integrable (fun children : Fin (rule.generation depth).edges →
        ((List (Fin rule.edges) × Bool) → Configuration rule.edges) => positiveRepresentative value (children leaf))
        ((independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) := by
    apply (integrable_map_measure (representativeMeasurable.comp (measurable_pi_apply leaf)).aestronglyMeasurable boundaryMeasurable.aemeasurable).mpr
    exact (innovationTreeShift_preserving rule p positive belowOne fixedPoint (generationEdgeAddress rule depth leaf)).integrable_comp_of_integrable representativeIntegrable
  have inverseInputIntegrable (leaf : Fin (rule.generation depth).edges) :
      Integrable (fun children : Fin (rule.generation depth).edges →
        ((List (Fin rule.edges) × Bool) → Configuration rule.edges) => (positiveRepresentative value (children leaf))⁻¹)
        ((independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) := by
    apply (integrable_map_measure (representativeMeasurable.inv.comp (measurable_pi_apply leaf)).aestronglyMeasurable boundaryMeasurable.aemeasurable).mpr
    exact (innovationTreeShift_preserving rule p positive belowOne fixedPoint (generationEdgeAddress rule depth leaf)).integrable_comp_of_integrable inverseRepresentativeIntegrable
  have inverseInputMean (leaf : Fin (rule.generation depth).edges) :
      (∫ children : Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges),
        (positiveRepresentative value (children leaf))⁻¹
        ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) = inverseMean := by
    have boundaryIntegral : (∫ children : Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges),
        (positiveRepresentative value (children leaf))⁻¹
        ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) =
        ∫ marks, (positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks))⁻¹
          ∂independentInnovationLaw rule p positive belowOne fixedPoint :=
      integral_map_of_stronglyMeasurable boundaryMeasurable
        (representativeMeasurable.inv.comp (measurable_pi_apply leaf)).stronglyMeasurable
    rw [boundaryIntegral]
    have shiftIntegral : (∫ marks, (positiveRepresentative value marks)⁻¹
        ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (innovationTreeShift rule (generationEdgeAddress rule depth leaf))) =
        ∫ marks, (positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks))⁻¹
          ∂independentInnovationLaw rule p positive belowOne fixedPoint :=
      integral_map_of_stronglyMeasurable
        (innovationTreeShift_measurable rule (generationEdgeAddress rule depth leaf)) representativeMeasurable.inv.stronglyMeasurable
    rw [(innovationTreeShift_preserving rule p positive belowOne fixedPoint (generationEdgeAddress rule depth leaf)).map_eq] at shiftIntegral
    exact shiftIntegral.symm.trans ((integral_congr_ae inverseEquality).trans inverseMeanEquality)
  have independent := innovationPrefix_frontier_independent rule p positive belowOne fixedPoint
    (generationEdgeAddress rule depth) (generationEdgeAddress_injective rule depth) (depth+1) (generationEdgeAddress_length rule depth)
  have conditional := independent_conditional_electrical_inverse_upper
    (independentInnovationLaw rule p positive belowOne fixedPoint) _ _ historyMeasurable boundaryMeasurable independent
    (rule.generation depth).network
    (fun data => markedGenerationConfiguration rule (innovationPrefixFill rule (depth+1) data) depth [] true)
    ((markedGenerationConfiguration_measurable rule depth [] true).comp (innovationPrefixFill_measurable rule (depth+1)))
    _ inputMeasurable (fun children leaf => positiveRepresentative_positive value (children leaf))
    inverseInputIntegrable inverseMean inverseMeanPositive inverseInputMean
  rw [coordinatePrefixFiltration_eq_comap]
  simpa only [markedGenerationConfiguration_prefix_factor] using conditional

theorem normalized_electrical_boundary_conditional_inverse_upper (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (inverseIntegrable : Integrable (fun marks => (value marks)⁻¹) (independentInnovationLaw rule p positive belowOne fixedPoint))
    (inverseMean : ℝ) (inverseMeanPositive : 0 < inverseMean)
    (inverseMeanEquality : (∫ marks, (value marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint) = inverseMean)
    (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      (independentInnovationLaw rule p positive belowOne fixedPoint)[
        fun marks => (((normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth+1] value) marks)⁻¹ |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks ≤
      inverseMean / electricalOrbitLp rule p positive belowOne fixedPoint growth (depth+1) marks := by
  have weighted := normalizedElectricalTransferLp_iterate_weighted_actual_ae rule p positive belowOne fixedPoint
    growth growthPositive.le value valuePositive depth
  have inverseEquality : (fun marks => (((normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth)^[depth+1] value) marks)⁻¹) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint]
      (growth^(depth+1)) • (fun marks => (electricalCell (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true)
        (fun leaf => positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)))⁻¹) := by
    filter_upwards [weighted] with marks equality
    rw [equality, mul_inv_rev]
    simp only [Pi.smul_apply, smul_eq_mul, inv_pow, inv_inv, mul_comm]
  have conditionalEquality := condExp_congr_ae (m := coordinatePrefixFiltration
    (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)) inverseEquality
  have scalarEquality := condExp_smul (μ := independentInnovationLaw rule p positive belowOne fixedPoint)
    (growth^(depth+1))
    (fun marks => (electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
      (fun leaf => positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)))⁻¹)
    (coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1))
  have upper := actual_electrical_boundary_conditional_inverse_upper rule p positive belowOne fixedPoint value valuePositive
    inverseIntegrable inverseMean inverseMeanPositive inverseMeanEquality depth
  filter_upwards [conditionalEquality, scalarEquality, upper,
    electricalOrbitLp_coe_ae_unit_generation rule p positive belowOne fixedPoint growth growthPositive.le depth]
    with marks conditional scalar inequality orbitEquality
  rw [conditional, scalar, Pi.smul_apply, smul_eq_mul, orbitEquality]
  calc
    _ ≤ growth^(depth+1)*(inverseMean/unitConfigurationResistance (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true)) :=
      mul_le_mul_of_nonneg_left inequality (pow_nonneg growthPositive.le _)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, inv_pow, inv_inv]; ring

theorem electricalOrbit_conditional_fixed_inverse_upper (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (valueFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    (inverseIntegrable : Integrable (fun marks => (value marks)⁻¹) (independentInnovationLaw rule p positive belowOne fixedPoint))
    (inverseMean : ℝ) (inverseMeanPositive : 0 < inverseMean)
    (inverseMeanEquality : (∫ marks, (value marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint) = inverseMean)
    (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      (independentInnovationLaw rule p positive belowOne fixedPoint)[fun marks => (value marks)⁻¹ |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks ≤
      inverseMean / electricalOrbitLp rule p positive belowOne fixedPoint growth (depth+1) marks := by
  have upper := normalized_electrical_boundary_conditional_inverse_upper rule p positive belowOne fixedPoint growth growthPositive
    value valuePositive inverseIntegrable inverseMean inverseMeanPositive inverseMeanEquality depth
  simpa only [Function.iterate_fixed valueFixed (depth+1)] using upper

theorem conditional_inverse_cauchy_schwarz
    {Sample : Type*} [ambient : MeasurableSpace Sample] (measure : Measure Sample) [IsFiniteMeasure measure]
    (subspace : MeasurableSpace Sample) (subspaceLe : subspace ≤ ambient)
    (value : Sample → ℝ) (valuePositive : ∀ᵐ sample ∂measure, 0 < value sample)
    (integrable : Integrable value measure) (inverseIntegrable : Integrable (fun sample => (value sample)⁻¹) measure) :
    ∀ᵐ sample ∂measure,
      0 < measure[value | subspace] sample ∧
      0 < measure[fun sample => (value sample)⁻¹ | subspace] sample ∧
      (measure[fun sample => (value sample)⁻¹ | subspace] sample)⁻¹ ≤ measure[value | subspace] sample := by
  have rationalBounds (coefficient : ℚ) : ∀ᵐ sample ∂measure,
      2*(coefficient : ℝ) ≤ measure[value | subspace] sample+
        (coefficient : ℝ)^2*measure[fun sample => (value sample)⁻¹ | subspace] sample := by
    have pointwise : (fun _ : Sample => 2*(coefficient : ℝ)) ≤ᵐ[measure]
        (fun sample => value sample+(coefficient : ℝ)^2*(value sample)⁻¹) := by
      filter_upwards [valuePositive] with sample positive
      apply (mul_le_mul_iff_of_pos_right positive).mp
      have cancellation : (coefficient : ℝ)^2*(value sample)⁻¹*value sample = (coefficient : ℝ)^2 := by
        rw [mul_assoc, inv_mul_cancel₀ positive.ne', mul_one]
      rw [add_mul, cancellation]
      nlinarith [sq_nonneg (value sample-(coefficient : ℝ))]
    have comparison := condExp_mono (m := subspace) (integrable_const (2*(coefficient : ℝ)))
      (integrable.add (inverseIntegrable.const_mul ((coefficient : ℝ)^2))) pointwise
    have sumEquality := condExp_add integrable (inverseIntegrable.const_mul ((coefficient : ℝ)^2)) subspace
    have scalarEquality := condExp_smul (μ := measure) ((coefficient : ℝ)^2) (fun sample => (value sample)⁻¹) subspace
    filter_upwards [comparison, sumEquality, scalarEquality] with sample inequality sum scalar
    rw [condExp_const subspaceLe] at inequality
    have scalar' : measure[fun sample => (coefficient : ℝ)^2*(value sample)⁻¹ | subspace] sample =
        (coefficient : ℝ)^2*measure[fun sample => (value sample)⁻¹ | subspace] sample := by
      simpa only [Pi.smul_def, Pi.smul_apply, smul_eq_mul] using scalar
    rw [sum, Pi.add_apply, scalar'] at inequality
    exact inequality
  have meanNonnegative := condExp_nonneg (m := subspace) (valuePositive.mono (fun _ positive => positive.le))
  have inverseNonnegative := condExp_nonneg (m := subspace)
    (valuePositive.mono (fun _ positive => (inv_pos.mpr positive).le))
  filter_upwards [ae_all_iff.mpr rationalBounds, meanNonnegative, inverseNonnegative] with sample bounds meanNonnegative inverseNonnegative
  simp only [Pi.zero_apply] at meanNonnegative inverseNonnegative
  have realBounds (coefficient : ℝ) : 2*coefficient ≤ measure[value | subspace] sample+
      coefficient^2*measure[fun sample => (value sample)⁻¹ | subspace] sample := by
    exact Rat.denseRange_cast.induction_on coefficient (isClosed_le (by fun_prop) (by fun_prop)) bounds
  have inversePositive : 0 < measure[fun sample => (value sample)⁻¹ | subspace] sample := by
    by_contra failure
    have zero : measure[fun sample => (value sample)⁻¹ | subspace] sample = 0 := le_antisymm (le_of_not_gt failure) inverseNonnegative
    have contradiction := realBounds (measure[value | subspace] sample+1)
    rw [zero, mul_zero, add_zero] at contradiction
    linarith
  have cancellation : (measure[fun sample => (value sample)⁻¹ | subspace] sample)⁻¹^2*
      measure[fun sample => (value sample)⁻¹ | subspace] sample =
      (measure[fun sample => (value sample)⁻¹ | subspace] sample)⁻¹ := by
    field_simp
  have comparison := realBounds ((measure[fun sample => (value sample)⁻¹ | subspace] sample)⁻¹)
  rw [cancellation] at comparison
  have inverseLe : (measure[fun sample => (value sample)⁻¹ | subspace] sample)⁻¹ ≤ measure[value | subspace] sample := by linarith
  exact ⟨(inv_pos.mpr inversePositive).trans_le inverseLe, inversePositive, inverseLe⟩

theorem electricalOrbit_conditional_fixed_reciprocal_sandwich (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (valueFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    (meanOne : (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1)
    (inverseIntegrable : Integrable (fun marks => (value marks)⁻¹) (independentInnovationLaw rule p positive belowOne fixedPoint))
    (inverseMean : ℝ) (inverseMeanPositive : 0 < inverseMean)
    (inverseMeanEquality : (∫ marks, (value marks)⁻¹ ∂independentInnovationLaw rule p positive belowOne fixedPoint) = inverseMean)
    (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      let conditionalMean := (independentInnovationLaw rule p positive belowOne fixedPoint)[⇑value |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks
      let conditionalInverse := (independentInnovationLaw rule p positive belowOne fixedPoint)[fun marks => (value marks)⁻¹ |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks
      0 < conditionalInverse ∧ conditionalMean ≤ electricalOrbitLp rule p positive belowOne fixedPoint growth (depth+1) marks ∧
      electricalOrbitLp rule p positive belowOne fixedPoint growth (depth+1) marks ≤ inverseMean/conditionalInverse ∧
      inverseMean/conditionalInverse ≤ inverseMean*conditionalMean := by
  have sandwich := electricalOrbit_conditional_fixed_sandwich rule p positive belowOne fixedPoint growth growthPositive.le
    value valuePositive valueFixed meanOne inverseIntegrable inverseMean inverseMeanPositive inverseMeanEquality depth
  have upper := electricalOrbit_conditional_fixed_inverse_upper rule p positive belowOne fixedPoint growth growthPositive
    value valuePositive valueFixed inverseIntegrable inverseMean inverseMeanPositive inverseMeanEquality depth
  have cauchy := conditional_inverse_cauchy_schwarz (independentInnovationLaw rule p positive belowOne fixedPoint)
    (coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1))
    ((coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)).le (depth+1))
    value valuePositive ((Lp.memLp value).integrable (by norm_num)) inverseIntegrable
  filter_upwards [sandwich, upper, cauchy] with marks bounds upper cauchy
  dsimp only
  refine ⟨cauchy.2.1, bounds.1, ?_, ?_⟩
  · apply (le_div_iff₀ cauchy.2.1).mpr
    have product := (le_div_iff₀ (cauchy.1.trans_le bounds.1)).mp upper
    simpa only [mul_comm] using product
  · simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left cauchy.2.2 inverseMeanPositive.le

end
end IGSIII34.Percolation
