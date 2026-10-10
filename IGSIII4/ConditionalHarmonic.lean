import IGSIII4.FiniteConditionalResponse
import IGSIII4.FrontierIndependence
import IGSIII4.RandomCellKernel
import IGSIII4.WeightedElectricalGeneration

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability IGSIII34.Percolation
open scoped NNReal

theorem generation_condExp_weightedResistance_lower_bound (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (measurable : Measurable value) (valuePositive : ∀ marks, 0 < (value marks : ℝ))
    (integrable : Integrable (fun marks => (value marks : ℝ))
      (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (inverseIntegrable : Integrable (fun marks => (value marks : ℝ)⁻¹)
      (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (inverseMeanPositive : 0 < ∫ marks, (value marks : ℝ)⁻¹
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint) (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      unitConfigurationResistance (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth [] true) /
        (∫ other, (value other : ℝ)⁻¹
          ∂independentInnovationLaw rule probability positive belowOne fixedPoint) ≤
      (condExp (innovationFiltration rule (depth + 1))
        (independentInnovationLaw rule probability positive belowOne fixedPoint)
        (fun marks => electricalCell (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth [] true)
          (fun leaf => (value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks) : ℝ)))) marks := by
  have frontierMeasurable : Measurable (fun marks leaf =>
      value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) :=
    measurable_pi_lambda _ (fun leaf => measurable.comp (innovationTreeShift_measurable rule _))
  have frontierIntegrable (leaf : Fin (rule.generation depth).edges) :
      Integrable (fun marks => (value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks) : ℝ))
        (independentInnovationLaw rule probability positive belowOne fixedPoint) :=
    (innovationTreeShift_preserving rule probability positive belowOne fixedPoint _).integrable_comp_of_integrable integrable
  have frontierInverseIntegrable (leaf : Fin (rule.generation depth).edges) :
      Integrable (fun marks => (value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks) : ℝ)⁻¹)
        (independentInnovationLaw rule probability positive belowOne fixedPoint) :=
    (innovationTreeShift_preserving rule probability positive belowOne fixedPoint _).integrable_comp_of_integrable inverseIntegrable
  have frontierInverseMean (leaf : Fin (rule.generation depth).edges) :
      (∫ marks, (value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks) : ℝ)⁻¹
        ∂independentInnovationLaw rule probability positive belowOne fixedPoint) =
      ∫ marks, (value marks : ℝ)⁻¹
        ∂independentInnovationLaw rule probability positive belowOne fixedPoint := by
    have inverseMeasurable : Measurable (fun marks => (value marks : ℝ)⁻¹) :=
      (measurable_coe_nnreal_real.comp measurable).inv
    have mapIdentity := integral_map_of_stronglyMeasurable
      (μ := independentInnovationLaw rule probability positive belowOne fixedPoint)
      (φ := innovationTreeShift rule (generationEdgeAddress rule depth leaf))
      (f := fun marks => (value marks : ℝ)⁻¹)
      (innovationTreeShift_measurable rule _) inverseMeasurable.stronglyMeasurable
    rw [(innovationTreeShift_preserving rule probability positive belowOne fixedPoint _).map_eq] at mapIdentity
    exact mapIdentity.symm
  have conditionalIdentity := condExp_finite_independent_response
    (independentInnovationLaw rule probability positive belowOne fixedPoint)
    (innovationFiltration rule (depth + 1)) ((innovationFiltration rule).le (depth + 1))
    (fun marks => markedGenerationConfiguration rule marks depth [] true)
    (markedGenerationConfiguration_prefix_measurable rule (depth + 1) depth [] true (by simp))
    (fun marks leaf => value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks))
    frontierMeasurable
    (generationFrontier_independent_filtration rule probability positive belowOne fixedPoint value measurable depth)
    (fun configuration input => (electricalCellNNReal (rule.generation depth).network configuration input : ℝ))
    (fun configuration => measurable_coe_nnreal_real.comp
      (electricalCellNNReal_continuous (rule.generation depth).network configuration).measurable)
    (fun configuration => electricalCellNNReal_integrable
      (independentInnovationLaw rule probability positive belowOne fixedPoint)
      (rule.generation depth).network configuration _ frontierMeasurable frontierIntegrable)
  filter_upwards [conditionalIdentity,
    independentInnovationLaw_crosses rule probability positive belowOne fixedPoint] with marks identity crossing
  change _ ≤ (condExp (innovationFiltration rule (depth + 1))
    (independentInnovationLaw rule probability positive belowOne fixedPoint)
    (fun marks => (electricalCellNNReal (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth [] true)
      (fun leaf => value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) : ℝ))) marks
  rw [identity]
  exact electricalCellNNReal_integral_lower_bound
    (independentInnovationLaw rule probability positive belowOne fixedPoint)
    (rule.generation depth).network _
    (markedGenerationConfiguration_crosses rule marks crossing depth [] true)
    _ frontierMeasurable (fun other leaf => valuePositive _)
    frontierIntegrable frontierInverseIntegrable inverseMeanPositive frontierInverseMean

theorem electricalTransfer_condExp_iterate_lower_bound (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0)
    (measurable : Measurable value) (valuePositive : ∀ marks, 0 < (value marks : ℝ))
    (integrable : Integrable (fun marks => (value marks : ℝ))
      (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (inverseIntegrable : Integrable (fun marks => (value marks : ℝ)⁻¹)
      (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (inverseMeanPositive : 0 < ∫ marks, (value marks : ℝ)⁻¹
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint) (depth : ℕ) :
    ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      unitConfigurationResistance (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth [] true) /
        (∫ other, (value other : ℝ)⁻¹
          ∂independentInnovationLaw rule probability positive belowOne fixedPoint) ≤
      (condExp (innovationFiltration rule (depth + 1))
        (independentInnovationLaw rule probability positive belowOne fixedPoint)
        ((electricalTransfer rule)^[depth + 1] (fun marks => (value marks : ℝ)))) marks := by
  have same : (electricalTransfer rule)^[depth + 1] (fun marks => (value marks : ℝ))
      =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint]
      fun marks => electricalCell (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth [] true)
        (fun leaf => (value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks) : ℝ)) := by
    filter_upwards [independentInnovationLaw_crosses rule probability positive belowOne fixedPoint] with marks crossing
    have emptyShift : innovationTreeShift rule [] marks = marks := by
      funext coordinate
      simp [innovationTreeShift]
    simpa only [emptyShift, List.nil_append] using
      electricalTransfer_iterate_eq_weighted_actual rule (fun marks => (value marks : ℝ)) valuePositive marks crossing depth []
  have sameConditional := condExp_congr_ae (m := innovationFiltration rule (depth + 1)) same
  filter_upwards [sameConditional, generation_condExp_weightedResistance_lower_bound rule probability
    positive belowOne fixedPoint value measurable valuePositive integrable inverseIntegrable inverseMeanPositive depth]
    with marks identity bound
  rw [identity]
  exact bound

end
end IGSIII4
