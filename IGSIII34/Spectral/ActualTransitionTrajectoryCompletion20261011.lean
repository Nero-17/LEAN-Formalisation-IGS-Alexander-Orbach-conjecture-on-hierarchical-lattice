import IGSIII34.Spectral.ActualTransitionKernelCompletion20261011
import IGSIII34.Spectral.TransitionTrajectoryMarginalsCompletion20261011
import IGSIII34.Spectral.ContinuousKernelTransitionIntegralCompletion20261011
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Actual transition kernels: positive times use the proved natural heat
kernel density and time zero is the identity kernel. Their continuous
expectations are precisely the constructed Feller semigroup. -/
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Preorder
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory ProbabilityTheory Filter InnerProductSpace IGSIII34.Diffusion
open scoped Topology BoundedContinuousFunction NNReal ProbabilityTheory
variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]

local instance actualTrajectoryNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualTrajectoryUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualTrajectoryTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualTrajectoryInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualTrajectoryCompleteCompletion20261011 :
    CompleteSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

variable [measure.IsOpenPosMeasure]
  (data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)

local instance actualTrajectoryAllMarkovCompletion20261011 :
    ∀ time, IsMarkovKernel (actualTransitionKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time) :=
  fun time => actualTransitionKernel_isMarkov_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time

def actualTransitionTrajectoryLawCompletion20261011
    (initial : Measure (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
    [IsProbabilityMeasure initial] (schedule : ℕ → ℝ≥0) :
    ProbabilityMeasure (ℕ → UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :=
  transitionTrajectoryLawCompletion20261011
    (actualTransitionKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data) initial schedule

theorem actualTransitionTrajectoryLaw_conditional_completion20261011
    (initial : Measure (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
    [IsProbabilityMeasure initial] (schedule : ℕ → ℝ≥0) (index : ℕ) :
    letI : Nonempty (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) := ⟨(anchor : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))⟩
    condDistrib (fun path : ℕ → UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) => path (index+1))
      (frestrictLe index) (actualTransitionTrajectoryLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data initial schedule : Measure (ℕ → UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))) =ᵐ[
        (actualTransitionTrajectoryLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data initial schedule : Measure (ℕ → UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))).map (frestrictLe index)]
      (actualTransitionKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data (schedule (index+1) - schedule index)).comap
        (fun history : Finset.Iic index → UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) => history ⟨index, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_pi_apply _) :=
by
  letI : Nonempty (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) := ⟨(anchor : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))⟩
  exact transitionTrajectoryLaw_conditional_completion20261011 _ initial schedule index

variable (denseDomain : Dense
  (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier)

include denseDomain in
theorem actualTransitionTrajectoryLaw_marginal_completion20261011
    (initial : Measure (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
    [IsProbabilityMeasure initial] (schedule : ℕ → ℝ≥0) (scheduleMonotone : Monotone schedule) (index : ℕ) :
    (actualTransitionTrajectoryLawCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data initial schedule : Measure (ℕ → UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))).map
      (fun path => path index) =
    actualTransitionKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data (schedule index) ∘ₘ initial :=
  transitionTrajectoryLaw_marginal_completion20261011 _
    (actualTransitionKernel_zero_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data)
    (actualTransitionKernel_add_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain)
    initial schedule scheduleMonotone index

end
end IGSIII34.Spectral
