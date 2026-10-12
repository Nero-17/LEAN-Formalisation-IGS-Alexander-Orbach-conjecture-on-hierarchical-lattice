import IGSIII34.Spectral.ActualCutoffNormLowerCompletion
import IGSIII34.Spectral.ActualLocalizedCutoffCompletion

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

/-- The actual cutoff quotient only requires its proved energy and square
integral estimates. A cell image/preimage identity is unnecessary. -/
theorem actual_completion_cutoff_quotient_lower_completion
    [measure.IsOpenPosMeasure]
    (potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks)
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (atPoint : actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point = 1)
    (energyBound massBound : ℝ)
    (energyEstimate : limitingEnergy
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val ≤ energyBound)
    (massEstimate : (∫ other,
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other^2
        ∂measure) ≤ massBound)
    (parameter : ℝ) (parameterPositive : 0 < parameter) :
    1 / (energyBound + parameter * massBound) ≤
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point^2 /
        (limitingEnergy
          (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
          parameter * ∫ other,
            actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other^2
              ∂measure) := by
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
  · exact add_le_add energyEstimate (mul_le_mul_of_nonneg_left massEstimate parameterPositive.le)

end
end IGSIII34.Spectral
