import IGSIII34.ResistanceLimit.ActualTraceUniqueness
import IGSIII34.Forms.CompletionTraceUniqueness
import IGSIII34.ResistanceLimit.ActualSkeletonEnergy

/-! The actual innovation-driven resistance form is determined by its finite
retained traces on the full metric completion among complete anchored function Hilbert spaces. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})

theorem actual_completed_form_unique_from_finite_traces
    {Energy : Type*} [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
    (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (evaluation : Energy →ₗ[ℝ]
      (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) → ℝ))
    (injective : Function.Injective evaluation)
    (spatialContinuous : ∀ potential, Continuous (evaluation potential))
    (continuous : ∀ point, Continuous (fun potential => evaluation potential point))
    (lower : ∀ boundary depth potential,
      (∀ vertex, evaluation potential ((actualTraceVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex) : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) =
        boundary (actualTraceVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)) →
      traceEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) depth boundary +
        boundary anchor ^ 2 ≤ ‖potential‖ ^ 2)
    (attained : ∀ boundary depth, ∃ potential,
      (∀ vertex, evaluation potential ((actualTraceVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex) : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) =
        boundary (actualTraceVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)) ∧
      ‖potential‖ ^ 2 = traceEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) depth boundary + boundary anchor ^ 2) :
    Set.range evaluation = {boundary | Continuous boundary ∧
      (fun point : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks => boundary (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))) ∈ energyDomain
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)} ∧
      ∀ potential, ‖potential‖ ^ 2 - evaluation potential (anchor : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) ^ 2 =
        limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) (fun point : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks => evaluation potential (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))) := by
  have restrictionInjective : Function.Injective (IGSIII34.Forms.completedFunctionRestriction evaluation) := by
    intro first last equal
    apply injective
    apply (UniformSpace.Completion.denseRange_coe (α := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)).equalizer
      (spatialContinuous first) (spatialContinuous last)
    exact equal
  have uniqueness := actual_form_unique_from_finite_traces rule p positive belowOne fixedPoint growth value growthPositive marks
    anchor (IGSIII34.Forms.completedFunctionRestriction evaluation) restrictionInjective
    (fun point => continuous (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
    lower attained
  refine ⟨?_, uniqueness.2⟩
  ext boundary
  constructor
  · rintro ⟨potential, rfl⟩
    refine ⟨spatialContinuous potential, ?_⟩
    have member := Set.mem_range_self (f := IGSIII34.Forms.completedFunctionRestriction evaluation) potential
    rw [uniqueness.1] at member
    exact member
  · rintro ⟨continuousBoundary, finiteEnergy⟩
    have member : (fun point : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks => boundary (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))) ∈
        Set.range (IGSIII34.Forms.completedFunctionRestriction evaluation) := by
      rw [uniqueness.1]
      exact finiteEnergy
    obtain ⟨potential, equal⟩ := member
    refine ⟨potential, ?_⟩
    apply (UniformSpace.Completion.denseRange_coe (α := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)).equalizer
      (spatialContinuous potential) continuousBoundary
    exact equal

end
end IGSIII34.ResistanceLimit
