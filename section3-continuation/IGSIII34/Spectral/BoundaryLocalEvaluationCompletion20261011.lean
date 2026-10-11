import IGSIII34.Spectral.ActualVariationalBoundsCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped Topology

theorem boundary_local_evaluation_global_integral_bound_completion20261011
    {Boundary : Type*} [MeasurableSpace Boundary]
    (boundary : Measure Boundary) [IsFiniteMeasure boundary]
    (function : Boundary → ℝ) (path : Boundary) (cylinder : Set Boundary)
    (cylinderMeasurable : MeasurableSet cylinder) (diameter energy : ℝ)
    (massPositive : 0 < boundary.real cylinder)
    (squareIntegrable : Integrable (fun other => function other^2) boundary)
    (oscillation : ∀ᵐ other ∂boundary.restrict cylinder,
      (function path - function other)^2 ≤ diameter * energy) :
    function path^2 ≤ 2 / boundary.real cylinder * (∫ other, function other^2 ∂boundary) +
      2 * diameter * energy := by
  have averaged := point_evaluation_le_of_resistance_inequality (boundary.restrict cylinder)
    function path diameter energy (by simpa only [Measure.real_def, Measure.restrict_apply_univ] using massPositive)
    squareIntegrable.restrict oscillation
  simp only [Measure.real_def, Measure.restrict_apply_univ] at averaged
  have integralBound := setIntegral_le_integral squareIntegrable
    (Eventually.of_forall (fun _ => sq_nonneg _)) (s := cylinder)
  have coefficientNonnegative : 0 ≤ (2 : ℝ) / boundary.real cylinder := div_nonneg (by norm_num) massPositive.le
  exact averaged.trans (add_le_add (mul_le_mul_of_nonneg_left integralBound coefficientNonnegative) le_rfl)

variable {Boundary : Type*} [MeasurableSpace Boundary]
  (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (boundary : Measure Boundary) [IsProbabilityMeasure boundary]
  (realization : Boundary → UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
  (realizationMeasurable : Measurable realization)

include realizationMeasurable in
theorem actual_boundary_completion_evaluation_quotient_upper_completion20261011
    (path : Boundary) (cylinder : Set Boundary) (cylinderMeasurable : MeasurableSet cylinder)
    (massPositive : 0 < boundary.real cylinder)
    (diameter : ℝ) (diameterNonnegative : 0 ≤ diameter)
    (diameterBound : ∀ᵐ other ∂boundary.restrict cylinder, dist (realization path) (realization other) ≤ diameter)
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential (realization path)^2 /
      (limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
        parameter * ∫ point, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point^2
          ∂(boundary.map realization)) ≤
      2 * max (1 / (parameter * boundary.real cylinder)) diameter := by
  letI : IsProbabilityMeasure (boundary.map realization) := Measure.isProbabilityMeasure_map realizationMeasurable.aemeasurable
  have squaredContinuous : Continuous (fun point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) =>
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point^2) :=
    (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential).continuous.pow 2
  have squareIntegrable := actual_completion_square_integrable_completion20261011 rule p positive belowOne fixedPoint growth value
    growthPositive marks (boundary.map realization) potential
  have pullIntegrable := (integrable_map_measure squaredContinuous.aestronglyMeasurable realizationMeasurable.aemeasurable).mp squareIntegrable
  have energyNonnegative := limitingEnergy_nonnegative
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) potential.property
  have evaluation := boundary_local_evaluation_global_integral_bound_completion20261011 boundary
    (fun other => actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential (realization other))
    path cylinder cylinderMeasurable diameter _ massPositive pullIntegrable (by
      filter_upwards [diameterBound] with other bound
      exact (actualEnergyExtension_resistance rule p positive belowOne fixedPoint growth value growthPositive
        marks potential (realization path) (realization other)).trans (mul_le_mul_of_nonneg_right bound energyNonnegative))
  have transport := integral_map_of_stronglyMeasurable (μ := boundary) realizationMeasurable squaredContinuous.stronglyMeasurable
  rw [← transport] at evaluation
  exact evaluation_quotient_le_component_bound _ _ _ _ _ _ energyNonnegative (integral_nonneg (fun _ => sq_nonneg _))
    massPositive parameterPositive diameterNonnegative evaluation

include realizationMeasurable in
theorem actual_boundary_diagonal_local_upper_completion20261011
    (path : Boundary) (cylinder : Set Boundary) (cylinderMeasurable : MeasurableSet cylinder)
    (massPositive : 0 < boundary.real cylinder)
    (diameter : ℝ) (diameterNonnegative : 0 ≤ diameter)
    (diameterBound : ∀ᵐ other ∂boundary.restrict cylinder, dist (realization path) (realization other) ≤ diameter)
    (parameter : ℝ) (parameterPositive : 0 < parameter) :
    actualDiagonalVariationalResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
      (boundary.map realization) parameter (realization path) ≤
      2 * max (1 / (parameter * boundary.real cylinder)) diameter := by
  apply csSup_le (Set.range_nonempty _)
  rintro result ⟨potential, rfl⟩
  exact actual_boundary_completion_evaluation_quotient_upper_completion20261011 rule p positive belowOne fixedPoint growth value
    growthPositive marks boundary realization realizationMeasurable path cylinder cylinderMeasurable massPositive diameter
    diameterNonnegative diameterBound parameter parameterPositive potential

end
end IGSIII34.Spectral
