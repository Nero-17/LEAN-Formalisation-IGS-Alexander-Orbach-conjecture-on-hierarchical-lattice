import IGSIII34.ResistanceLimit.ActualSkeletonEnergy
import IGSIII34.Forms.AnchoredHilbert
import IGSIII34.Forms.CompletionExtension

/-! Actual retained stationary energies: complete anchored energy space and
the injective continuous-extension domain on its electrical completion. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})

def actualEnergyDomain : Submodule ℝ
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks → ℝ) :=
  energyDomain (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)

@[reducible] def actualAnchoredNormedAddCommGroup
    (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) :
    NormedAddCommGroup (actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :=
  anchoredNormedAddCommGroup
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_traceEnergy_monotone rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks) anchor

theorem actual_anchored_completeSpace
    (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) :
    letI := actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
    letI : UniformSpace (actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :=
      (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
    CompleteSpace (actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :=
  anchored_completeSpace
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_traceEnergy_monotone rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks) anchor

@[reducible] def actualAnchoredInnerProductSpace
    (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) :
    letI := actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
    InnerProductSpace ℝ (actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) :=
  anchoredInnerProductSpace
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_traceEnergy_monotone rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks) anchor

def actualEnergyExtensionLinear :
    (actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks) →ₗ[ℝ]
      C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ) :=
  completionExtensionLinear
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)

theorem actualEnergyExtensionLinear_injective :
    Function.Injective (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks) :=
  completionExtensionLinear_injective
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)

theorem actualEnergyExtension_resistance
    (potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks)
    (first second : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential first -
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential second) ^ 2 ≤
        dist first second * limitingEnergy
          (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val :=
  completionExtension_resistance
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)
    potential first second

end
end IGSIII34.Forms
