import IGSIII34.Spectral.ActualScalarSpeedKernelCompletion
import IGSIII34.Diffusion.GlobalTimeRescaleCouplingCompletion

/-! Actual transition kernels: positive times use the proved natural heat
kernel density and time zero is the identity kernel. Their continuous
expectations are precisely the constructed Feller semigroup. -/
set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory ProbabilityTheory Filter InnerProductSpace IGSIII34.Diffusion
open scoped Topology BoundedContinuousFunction NNReal ProbabilityTheory
theorem actualScalarSpeedTime_inverse_ratio_completion
    (constant : ℝ) (constantPositive : 0 < constant) (time : ℝ≥0) :
    actualScalarSpeedTimeCompletion constant constantPositive time =
      Real.toNNReal constant⁻¹ * time := by
  apply Subtype.ext
  change (time : ℝ) / constant = (Real.toNNReal constant⁻¹ : ℝ) * (time : ℝ)
  rw [Real.coe_toNNReal _ (inv_nonneg.mpr constantPositive.le)]
  rw [div_eq_mul_inv, mul_comm]

theorem actualScalarSpeedTime_add_completion
    (constant : ℝ) (constantPositive : 0 < constant) (first second : ℝ≥0) :
    actualScalarSpeedTimeCompletion constant constantPositive (first + second) =
      actualScalarSpeedTimeCompletion constant constantPositive first +
        actualScalarSpeedTimeCompletion constant constantPositive second := by
  apply Subtype.ext
  change ((first : ℝ) + (second : ℝ)) / constant = (first : ℝ) / constant + (second : ℝ) / constant
  exact add_div _ _ _

/-- The actual limiting path time scale used by the deterministic-clock
theorem is literally evaluation of B at t/C. -/
theorem scalarSpeedGlobalTimeScale_evaluation_completion
    {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    (constant : ℝ) (constantPositive : 0 < constant)
    (path : SkorokhodGlobalPathCompletion Space) (time : ℝ≥0) :
    skorokhodGlobalTimeScaleCompletion
      (Real.toNNReal constant⁻¹) path time =
      path (actualScalarSpeedTimeCompletion constant constantPositive time) := by
  change path (Real.toNNReal constant⁻¹ * time) = _
  rw [← actualScalarSpeedTime_inverse_ratio_completion]

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]

local instance actualScalarSpeedProcessNormCompletion :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualScalarSpeedProcessUniformCompletion :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualScalarSpeedProcessTopologyCompletion :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualScalarSpeedProcessInnerCompletion :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualScalarSpeedProcessCompleteCompletion :
    CompleteSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

variable [measure.IsOpenPosMeasure]
  (data : ActualSpectralDataCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)

variable (denseDomain : Dense
  (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier)

include denseDomain in
theorem actualScalarSpeedTransitionKernel_add_completion
    (constant : ℝ) (constantPositive : 0 < constant) (first second : ℝ≥0) :
    (actualScalarSpeedTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data constant constantPositive second) ∘ₖ
      (actualScalarSpeedTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data constant constantPositive first) =
    actualScalarSpeedTransitionKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data constant constantPositive (first + second) := by
  simp only [actualScalarSpeedTransitionKernel_identity_completion, actualScalarSpeedTime_add_completion]
  exact actualTransitionKernel_add_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data denseDomain _ _

end
end IGSIII34.Spectral

