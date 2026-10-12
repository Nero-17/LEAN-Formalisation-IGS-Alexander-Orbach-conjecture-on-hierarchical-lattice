import IGSIII34.Spectral.ActualPositiveParameterResolvent20261011
import IGSIII34.Spectral.ActualResolventConservationCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory Filter InnerProductSpace
open scoped Topology BoundedContinuousFunction

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]

local instance actualNonzeroSupremumNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualNonzeroSupremumUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualNonzeroSupremumTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualNonzeroSupremumInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualNonzeroSupremumCompleteCompletion20261011 :
    CompleteSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

/-- Deleting the zero input does not change a real supremum when a nonzero
input has value at least the value at zero. Cofinality avoids any additional
boundedness assumption. -/
theorem real_supremum_remove_zero_completion20261011 {Domain : Type*} [Zero Domain]
    (quotient : Domain → ℝ) (atZero : quotient 0 = 0)
    (witness : Domain) (witnessNonzero : witness ≠ 0)
    (witnessNonnegative : 0 ≤ quotient witness) :
    sSup (Set.range quotient) = sSup (quotient '' {potential | potential ≠ 0}) := by
  apply csSup_eq_csSup_of_forall_exists_le
  · rintro result ⟨potential, rfl⟩
    by_cases zero : potential = 0
    · exact ⟨quotient witness, ⟨witness, witnessNonzero, rfl⟩,
        by simpa only [zero, atZero] using witnessNonnegative⟩
    · exact ⟨quotient potential, ⟨potential, zero, rfl⟩, le_rfl⟩
  · rintro result ⟨potential, _, rfl⟩
    exact ⟨quotient potential, ⟨potential, rfl⟩, le_rfl⟩

include anchor in
/-- The literal actual-energy quotient can be restricted to nonzero
potentials, exactly as in the manuscript's variational formula. -/
theorem actual_positive_variational_supremum_nonzero_completion20261011
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (parameter : ℝ) (parameterPositive : 0 < parameter) :
    actualDiagonalVariationalResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure parameter point =
      sSup ((fun potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks =>
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point ^ 2 /
          (limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
            (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
            parameter * ∫ other, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other ^ 2 ∂measure)) ''
        {potential | potential ≠ 0}) := by
  unfold actualDiagonalVariationalResolventCompletion20261011
  refine real_supremum_remove_zero_completion20261011 _ ?_
    (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor 1) ?_ ?_
  · simp only [map_zero, ContinuousMap.zero_apply, zero_pow (by decide : 2 ≠ 0), zero_div]
  · intro equality
    have evaluated := congrArg (fun potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks =>
      potential.val anchor) equality
    simp [actualEnergyConstantCompletion20261011] at evaluated
  · exact div_nonneg (sq_nonneg _)
      (add_nonneg (limitingEnergy_nonnegative
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor 1).property)
        (mul_nonneg parameterPositive.le (integral_nonneg (fun _ => sq_nonneg _))))

variable [measure.IsOpenPosMeasure]
  (data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)

/-- All-positive diagonal Laplace identity with the manuscript's explicit
supremum over nonzero functions. The kernel and energy are the actual
constructed objects; no identity or convergence conclusion is an input. -/
theorem actual_positive_laplace_variational_nonzero_completion20261011
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (parameter : ℝ) (parameterPositive : 0 < parameter) :
    diagonalLaplace (fun time => actualSpectralHeatKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time point point) parameter =
      sSup ((fun potential : actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks =>
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point ^ 2 /
          (limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
            (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val +
            parameter * ∫ other, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential other ^ 2 ∂measure)) ''
        {potential | potential ≠ 0}) := by
  exact (actualSpectralData_positive_laplace_variational_completion20261011
    rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data point parameter parameterPositive).trans
      (actual_positive_variational_supremum_nonzero_completion20261011
        rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure point parameter parameterPositive)

end
end IGSIII34.Spectral


