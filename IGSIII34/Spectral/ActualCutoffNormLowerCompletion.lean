import IGSIII34.Spectral.ActualLocalEvaluationCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped Topology

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

theorem actual_supported_completion_cutoff_square_integral_completion
    (potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks)
    (cell : Set (UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
    (cellMeasurable : MeasurableSet cell)
    (range : ∀ other,
      0 ≤ actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other ∧
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other ≤ 1)
    (vanishes : ∀ other ∉ cell,
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other = 0) :
    (∫ other,
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other^2
        ∂measure) ≤ measure.real cell := by
  classical
  have comparison : ∀ other,
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other^2 ≤
        cell.indicator (fun _ => (1 : ℝ)) other := by
    intro other
    by_cases member : other ∈ cell
    · rw [Set.indicator_of_mem member]
      obtain ⟨nonnegative, belowOne⟩ := range other
      nlinarith
    · rw [Set.indicator_of_notMem member, vanishes other member]
      norm_num
  have bounded := integral_mono_ae
    (actual_completion_square_integrable_completion rule p positive belowOne fixedPoint
      growth value growthPositive marks measure potential)
    ((integrable_const (1 : ℝ)).indicator cellMeasurable)
    (Eventually.of_forall comparison)
  rw [integral_indicator cellMeasurable] at bounded
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using bounded

/-- A continuous actual finite-energy cutoff which equals one at the point
and vanishes off its parent cell supplies the lower variational bound.
Its energy is the actual limiting trace energy, rather than an abstract form input. -/
theorem actual_supported_completion_cutoff_quotient_lower_completion
    [measure.IsOpenPosMeasure]
    (potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks)
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (atPoint : actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point = 1)
    (cell : Set (UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
    (cellMeasurable : MeasurableSet cell)
    (range : ∀ other,
      0 ≤ actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other ∧
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other ≤ 1)
    (vanishes : ∀ other ∉ cell,
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other = 0)
    (bound : ℝ)
    (energyBound : limitingEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val ≤ bound)
    (parameter : ℝ) (parameterPositive : 0 < parameter) :
    1 / (bound + parameter * measure.real cell) ≤
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point^2 /
        (limitingEnergy
          (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
          parameter * ∫ other,
            actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other^2
              ∂measure) := by
  have normBound := actual_supported_completion_cutoff_square_integral_completion
    rule p positive belowOne fixedPoint growth value growthPositive marks measure potential cell cellMeasurable range vanishes
  have integralPositive : 0 < ∫ other,
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other^2
        ∂measure := by
    apply integral_pos_of_integrable_nonneg_nonzero (x := point)
      ((actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential).continuous.pow 2)
      (actual_completion_square_integrable_completion rule p positive belowOne fixedPoint
        growth value growthPositive marks measure potential)
      (fun other => sq_nonneg _)
    change actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point^2 ≠ 0
    rw [atPoint]
    norm_num
  have energyNonnegative := limitingEnergy_nonnegative
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) potential.property
  rw [atPoint, one_pow]
  apply one_div_le_one_div_of_le
  · exact add_pos_of_nonneg_of_pos energyNonnegative (mul_pos parameterPositive integralPositive)
  · exact add_le_add energyBound (mul_le_mul_of_nonneg_left normBound parameterPositive.le)

end
end IGSIII34.Spectral
