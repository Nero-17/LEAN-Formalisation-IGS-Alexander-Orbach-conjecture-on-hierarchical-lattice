import IGSIII34.Diffusion.ActualContinuousObjectiveCompletion
import IGSIII34.Spectral.ActualDiagonalResolventCompletion
import IGSIII34.Spectral.ActualResolventPositivityCompletion
import IGSIII34.Diffusion.CoerciveObjectiveCompletion
import IGSIII34.Diffusion.ActualNormalizedResolventCompletion
import IGSIII34.Spectral.ActualResolventMarkovCompletion
import IGSIII34.Spectral.ContinuousLpOrderCompletion
import Mathlib.MeasureTheory.Function.LpOrder

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open IGSIII34.Spectral
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory Filter InnerProductSpace IGSIII34.Diffusion
open scoped Topology BoundedContinuousFunction
variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]

local instance ActualWholeContinuousResolventCompletionNorm :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualWholeContinuousResolventCompletionUniform :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance ActualWholeContinuousResolventCompletionTopology :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ActualWholeContinuousResolventCompletionInner :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualWholeContinuousResolventCompletionComplete :
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

def actualNormalizedContinuousResolventCompletion
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) :
    C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ) →L[ℝ]
      C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ) :=
  parameter • (actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).comp
    ((parameterEnergySolutionCompletion
      (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
      (actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      parameter parameterAtLeastOne).comp (ContinuousMap.toLp 2 measure ℝ))

theorem actualNormalizedContinuousResolvent_solution_completion
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    actualNormalizedContinuousResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne forcing = parameter •
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (actualContinuousEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        parameter parameterAtLeastOne forcing) := rfl

theorem actualNormalizedContinuousResolvent_supnorm_completion
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    ‖actualNormalizedContinuousResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne forcing‖ ≤ ‖forcing‖ := by
  apply continuousMap_operator_norm_bound_completion measure
    (parameter • actualParameterL2ResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne)
    (actual_normalized_parameter_resolvent_positive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne)
  · intro constant
    have constantImage : ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const _ constant) =
        actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
          (actualEnergyConstantCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant) := by
      have equality : (ContinuousMap.const _ constant) =
          actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor
            (actualEnergyConstantCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant) := by
        ext point
        exact (actualEnergyConstant_extension_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant point).symm
      rw [equality]
      rfl
    rw [constantImage]
    exact actual_normalized_parameter_resolvent_constant_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne constant
  · change ContinuousMap.toLp 2 measure ℝ (parameter • actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor
      (parameterEnergySolutionCompletion (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) (actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) parameter parameterAtLeastOne (ContinuousMap.toLp 2 measure ℝ forcing))) = _
    rw [map_smul]
    rfl

theorem actualNormalizedContinuousResolvent_energy_calibration_completion
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    actualNormalizedContinuousResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne
      (actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor forcing) =
    actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor
      (actualNormalizedResolventSolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        parameter parameterAtLeastOne forcing) := by
  change parameter • actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor
    (parameterEnergySolutionCompletion (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) (actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) parameter parameterAtLeastOne
      (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure forcing)) = _
  rw [← map_smul]
  congr 1
  simp only [actualNormalizedResolventSolutionCompletion, normalizedAnchoredResolventSolutionCompletion,
    parameterEnergySolutionCompletion, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, map_smul]

theorem contraction_converges_on_dense_range_completion
    {Domain Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (operators : ℕ → Target →L[ℝ] Target)
    (contractive : ∀ index value, ‖operators index value‖ ≤ ‖value‖)
    (embedding : Domain → Target) (dense : DenseRange embedding)
    (denseConvergence : ∀ value, Tendsto (fun index => operators index (embedding value)) atTop (𝓝 (embedding value)))
    (value : Target) : Tendsto (fun index => operators index value) atTop (𝓝 value) := by
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  obtain ⟨approximation, close⟩ := Metric.denseRange_iff.mp dense value (epsilon / 3) (by positivity)
  have eventual : ∀ᶠ index in atTop, dist (operators index (embedding approximation)) (embedding approximation) < epsilon / 3 :=
    (denseConvergence approximation).eventually (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [eventual] with index nearby
  have first : dist (operators index value) (operators index (embedding approximation)) ≤ dist value (embedding approximation) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact contractive index _
  have triangle := (dist_triangle (operators index value) (operators index (embedding approximation)) value).trans
    (add_le_add le_rfl (dist_triangle (operators index (embedding approximation)) (embedding approximation) value))
  rw [dist_comm (embedding approximation) value] at triangle
  linarith

theorem actualNormalizedContinuousResolvent_uniform_tendsto_completion
    (denseDomain : Dense
      (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier)
    (parameters : ℕ → ℝ) (parametersAtLeastOne : ∀ index, 1 ≤ parameters index)
    (parametersDiverge : Tendsto parameters atTop atTop)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    Tendsto (fun index => parameters index •
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
        (actualContinuousEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
          (parameters index) (parametersAtLeastOne index) forcing)) atTop (𝓝 forcing) := by
  have domainRange := completionEnergyDomain_eq_extension_range
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)
  have denseEmbedding : DenseRange (actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) := by
    change Dense (Set.range (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks))
    exact (congrArg Dense domainRange).mp denseDomain
  apply contraction_converges_on_dense_range_completion
    (fun index => actualNormalizedContinuousResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (parameters index) (parametersAtLeastOne index))
    (fun index => actualNormalizedContinuousResolvent_supnorm_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (parameters index) (parametersAtLeastOne index)) _ denseEmbedding
  intro potential
  have uniform := actualNormalizedResolventSolution_uniform_tendsto_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    parameters parametersAtLeastOne parametersDiverge potential
  have converted := (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ).symm.continuous.tendsto
    (actualEnergyBoundedEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential)
      |>.comp uniform
  simpa only [actualNormalizedContinuousResolvent_energy_calibration_completion,
    actualEnergyBoundedEmbeddingCompletion, ContinuousLinearMap.comp_apply, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using converted

end
end IGSIII34.Diffusion



