import IGSIII34.Spectral.ActualEvaluationCompletion20261011
import IGSIII34.Spectral.ComponentResolvent
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped Topology

theorem local_point_evaluation_global_integral_bound_completion20261011
    {Space : Type*} [MeasurableSpace Space]
    (measure : Measure Space) [IsFiniteMeasure measure]
    (function : Space → ℝ) (point : Space) (cell : Set Space)
    (cellMeasurable : MeasurableSet cell) (diameter energy : ℝ)
    (massPositive : 0 < measure.real cell)
    (squareIntegrable : Integrable (fun other => function other^2) measure)
    (oscillation : ∀ other ∈ cell, (function point - function other)^2 ≤ diameter * energy) :
    function point^2 ≤ 2 / measure.real cell *
      (∫ other, function other^2 ∂measure) + 2 * diameter * energy := by
  have restrictedMass : (measure.restrict cell).real Set.univ = measure.real cell := by
    simp only [Measure.real_def, Measure.restrict_apply_univ]
  have averaged := point_evaluation_le_of_resistance_inequality
    (measure.restrict cell) function point diameter energy (by rw [restrictedMass]; exact massPositive)
    squareIntegrable.restrict ((ae_restrict_mem cellMeasurable).mono (fun other member => oscillation other member))
  rw [restrictedMass] at averaged
  apply averaged.trans
  have integralBound := setIntegral_le_integral squareIntegrable
    (Eventually.of_forall (fun other => sq_nonneg (function other))) (s := cell)
  simpa only [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left integralBound
    (show (0 : ℝ) ≤ 2 / measure.real cell from div_nonneg (by norm_num) massPositive.le)) (2 * diameter * energy)

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
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
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

theorem actual_completion_square_integrable_completion20261011
    (potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :
    Integrable (fun point =>
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point^2) measure := by
  let squared : C(UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ) :=
    ⟨_, (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential).continuous.pow 2⟩
  exact ((BoundedContinuousFunction.mkOfCompact squared).integrable measure).congr
    (Eventually.of_forall (fun _ => rfl))

theorem actual_local_completion_resolvent_evaluation_bound_completion20261011
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (cell : Set (UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
    (cellMeasurable : MeasurableSet cell) (diameter : ℝ) (diameterNonnegative : 0 ≤ diameter)
    (diameterBound : ∀ other ∈ cell, dist point other ≤ diameter)
    (massPositive : 0 < measure.real cell)
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point^2 /
      (limitingEnergy
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
        parameter * ∫ other,
          actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other^2
            ∂measure) ≤
      2 * max (1 / (parameter * measure.real cell)) diameter := by
  have energyNonnegative := limitingEnergy_nonnegative
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) potential.property
  have evaluation := local_point_evaluation_global_integral_bound_completion20261011 measure
    (fun point => actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point)
    point cell cellMeasurable diameter _ massPositive
    (actual_completion_square_integrable_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure potential)
    (fun other member => (actualEnergyExtension_resistance rule p positive belowOne fixedPoint growth value growthPositive
      marks potential point other).trans (mul_le_mul_of_nonneg_right (diameterBound other member) energyNonnegative))
  exact evaluation_quotient_le_component_bound _ _ _ _ _ _ energyNonnegative
    (integral_nonneg (fun _ => sq_nonneg _)) massPositive parameterPositive diameterNonnegative evaluation

theorem actual_resistance_ball_resolvent_evaluation_bound_completion20261011
    [measure.IsOpenPosMeasure]
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (radius : ℝ) (radiusPositive : 0 < radius)
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point^2 /
      (limitingEnergy
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
        parameter * ∫ other,
          actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other^2
            ∂measure) ≤
      2 * max (1 / (parameter * measure.real (Metric.ball point radius))) radius := by
  apply actual_local_completion_resolvent_evaluation_bound_completion20261011 rule p positive belowOne fixedPoint
    growth value growthPositive marks measure point (Metric.ball point radius) Metric.isOpen_ball.measurableSet radius radiusPositive.le
  · intro other member
    have bound := Metric.mem_ball.mp member
    rw [dist_comm] at bound
    exact bound.le
  · exact ENNReal.toReal_pos (Metric.measure_ball_pos measure point radiusPositive).ne' (measure_ne_top _ _)
  · exact parameterPositive

end
end IGSIII34.Spectral
