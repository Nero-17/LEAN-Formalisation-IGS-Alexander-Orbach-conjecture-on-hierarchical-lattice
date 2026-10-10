import IGSIII34.Percolation.Continuation.ElectricalBoundarySecondMoment
import IGSIII34.Percolation.Continuation.ElectricalLawMixtureVariance

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution
open scoped NNReal ENNReal BigOperators

def electricalBoundaryGenerationVariance (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (depth : ℕ) : ℝ :=
  ∫ configuration, ∫ input : Fin (rule.generation depth).edges → ℝ≥0,
    (electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ)) -
      ∫ input : Fin (rule.generation depth).edges → ℝ≥0,
        electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))
          ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))^2
      ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0))
      ∂((independentInnovationLaw rule p positive belowOne fixedPoint).map
        (fun marks => markedGenerationConfiguration rule marks depth [] true))

theorem electricalBoundaryGenerationVariance_nonnegative (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (depth : ℕ) :
    0 ≤ electricalBoundaryGenerationVariance rule p positive belowOne fixedPoint law depth :=
  integral_nonneg (fun _ => integral_nonneg (fun _ => sq_nonneg _))

theorem electrical_eigenlaw_generation_boundary_variance_bound (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (moments : ∀ exponent : ℝ, Integrable (fun value : ℝ≥0 => (value:ℝ)^exponent) (law:Measure ℝ≥0))
    (growth : ℝ≥0)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power) (depth : ℕ) :
    electricalBoundaryGenerationVariance rule p positive belowOne fixedPoint law depth ≤
      2*(∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)) *
        ((growth:ℝ)^(2*(depth+1))*(∫ value : ℝ≥0, (value:ℝ)^2 ∂(law:Measure ℝ≥0)))^(1/(2:ℝ)) *
        (((rule.generation depth).edges:ℝ)*(∫ value : ℝ≥0, (value:ℝ)⁻¹^power ∂(law:Measure ℝ≥0)))^(1/power) := by
  let configurationLaw := (independentInnovationLaw rule p positive belowOne fixedPoint).map
    (fun marks => markedGenerationConfiguration rule marks depth [] true)
  letI : IsProbabilityMeasure configurationLaw := Measure.isProbabilityMeasure_map
    (markedGenerationConfiguration_measurable rule depth [] true).aemeasurable
  have secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0) := by
    simpa only [Real.rpow_two] using moments 2
  have supported : ∀ configuration, (rule.generation depth).network.crosses configuration ≠ true →
      configurationLaw {configuration} = 0 := by
    have crossing : ∀ᵐ configuration ∂configurationLaw, (rule.generation depth).network.crosses configuration = true := by
      apply (ae_map_iff (markedGenerationConfiguration_measurable rule depth [] true).aemeasurable
        (measurableSet_eq_fun (measurable_of_countable _) measurable_const)).mpr
      filter_upwards [independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks crosses
      exact markedGenerationConfiguration_crosses rule marks crosses depth [] true
    intro configuration notCrossing
    apply measure_mono_null _ (ae_iff.mp crossing)
    intro candidate member
    have equality : candidate = configuration := Set.mem_singleton_iff.mp member
    subst candidate
    exact notCrossing
  have centralEquality (configuration : Configuration (rule.generation depth).edges) :
      (∫ input : Fin (rule.generation depth).edges → ℝ≥0,
        (electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ)) -
          ∫ input : Fin (rule.generation depth).edges → ℝ≥0,
            electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))
              ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))^2
          ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0))) =
        (∫ input : Fin (rule.generation depth).edges → ℝ≥0,
          electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))^2
            ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0))) -
          (∫ input : Fin (rule.generation depth).edges → ℝ≥0,
            electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))
              ∂Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0)))^2 := by
    have measurable : Measurable (fun input : Fin (rule.generation depth).edges → ℝ≥0 =>
        electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))) :=
      (NNReal.continuous_coe.comp (electricalCellNNReal_continuous (rule.generation depth).network configuration)).measurable
    have memLp : MemLp (fun input : Fin (rule.generation depth).edges → ℝ≥0 =>
        electricalCell (rule.generation depth).network configuration (fun edge => (input edge:ℝ))) 2
        (Measure.pi (fun _ : Fin (rule.generation depth).edges => (law:Measure ℝ≥0))) :=
      (memLp_two_iff_integrable_sq measurable.aestronglyMeasurable).mpr
        (electricalCell_nnreal_square_integrable (rule.generation depth).network configuration law secondMoment)
    rw [← variance_eq_integral measurable.aemeasurable, variance_eq_sub memLp]
    rfl
  unfold electricalBoundaryGenerationVariance
  simp_rw [centralEquality]
  have bound := electricalCell_law_mixture_variance_le_product_moments
    (rule.generation depth).network configurationLaw supported law lawPositive moments powerAtLeastTwo
  rw [electricalBoundaryTree_eigenlaw_generation_second_moment rule p positive belowOne fixedPoint law lawPositive
    secondMoment growth eigenlaw depth] at bound
  exact bound

end
end IGSIII34.Percolation
