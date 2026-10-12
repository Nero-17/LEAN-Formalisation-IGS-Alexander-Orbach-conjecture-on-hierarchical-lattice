import IGSIII34.Diffusion.ActualContinuousObjectiveCompletion
import IGSIII34.Diffusion.CoerciveObjectiveApproximationCompletion
import IGSIII34.Spectral.ActualHarmonicAnchoredCompletion
import IGSIII34.Spectral.ActualDiagonalResolventCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
namespace IGSIII34.Diffusion
noncomputable section
open IGSIII34.Diffusion IGSIII34.Spectral
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))]

local instance actualHarmonicObjectiveUniqueNormCompletion : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualHarmonicObjectiveUniqueUniformCompletion : UniformSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualHarmonicObjectiveUniqueNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualHarmonicObjectiveUniqueTopologyCompletion : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualHarmonicObjectiveUniqueNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualHarmonicObjectiveUniqueInnerCompletion : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualHarmonicObjectiveUniqueCompleteCompletion : CompleteSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor


variable [MeasurableSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))]
  [BorelSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))]
  (measure : Measure (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))))
  [IsProbabilityMeasure measure]


variable [measure.IsOpenPosMeasure]

/-- Comparison with the constructed harmonic interpolants of the true
variational solution identifies a finite-resolvent candidate uniquely. -/
theorem actualContinuousEnergySolution_unique_of_harmonic_comparison_completion
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)), ℝ))
    (candidate : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor)
    (comparison : ∀ depth, coerciveObjectiveCompletion (parameterAnchoredResolventBilinearCompletion (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure) (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) parameter) (actualContinuousForcingDualCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure forcing) candidate ≤
      coerciveObjectiveCompletion (parameterAnchoredResolventBilinearCompletion (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure) (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) parameter) (actualContinuousForcingDualCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure forcing) (actualAnchoredHarmonicInterpolationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor depth (actualContinuousEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure parameter parameterAtLeastOne forcing))) :
    candidate = (actualContinuousEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure parameter parameterAtLeastOne forcing) := by
  apply coerciveObjective_minimizer_unique_completion _
    (parameterAnchoredResolventBilinear_coercive_completion (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure) (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) (actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure) parameter parameterAtLeastOne)
    _ (parameterAnchoredResolventBilinear_symmetric_completion (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure) (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) parameter)
    _ (fun test => actualContinuousEnergySolution_variational_completion
      rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure parameter parameterAtLeastOne forcing test) candidate
  exact coerciveObjective_comparison_of_approximation_completion _ _ candidate _ _
    (actual_harmonic_interpolation_anchored_tendsto_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor (actualContinuousEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure parameter parameterAtLeastOne forcing)) comparison

end
end IGSIII34.Diffusion
