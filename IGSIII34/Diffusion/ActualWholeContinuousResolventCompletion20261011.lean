import IGSIII34.Diffusion.ActualContinuousObjectiveCompletion20261011
import IGSIII34.Spectral.ActualDiagonalResolventCompletion20261011
import IGSIII34.Spectral.ActualResolventPositivityCompletion20261011
import IGSIII34.Diffusion.CoerciveObjectiveCompletion20261011
import IGSIII34.Diffusion.ActualNormalizedResolventCompletion20261011
import IGSIII34.Spectral.ActualResolventMarkovCompletion20261011
import IGSIII34.Spectral.ContinuousLpOrderCompletion20261011
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

local instance ActualWholeContinuousResolventCompletion20261011Norm :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualWholeContinuousResolventCompletion20261011Uniform :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance ActualWholeContinuousResolventCompletion20261011Topology :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ActualWholeContinuousResolventCompletion20261011Inner :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualWholeContinuousResolventCompletion20261011Complete :
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

def actualNormalizedContinuousResolventCompletion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) :
    C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ) →L[ℝ]
      C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ) :=
  parameter • (actualEnergyContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor).comp
    ((parameterEnergySolutionCompletion20261011
      (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
      (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      parameter parameterAtLeastOne).comp (ContinuousMap.toLp 2 measure ℝ))

theorem actualNormalizedContinuousResolvent_solution_completion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    actualNormalizedContinuousResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne forcing = parameter •
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        parameter parameterAtLeastOne forcing) := rfl

theorem actualNormalizedContinuousResolvent_supnorm_completion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    ‖actualNormalizedContinuousResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne forcing‖ ≤ ‖forcing‖ := by
  apply continuousMap_operator_norm_bound_completion20261011 measure
    (parameter • actualParameterL2ResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne)
    (actual_normalized_parameter_resolvent_positive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne)
  · intro constant
    have constantImage : ContinuousMap.toLp 2 measure ℝ (ContinuousMap.const _ constant) =
        actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
          (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant) := by
      have equality : (ContinuousMap.const _ constant) =
          actualEnergyContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor
            (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant) := by
        ext point
        exact (actualEnergyConstant_extension_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant point).symm
      rw [equality]
      rfl
    rw [constantImage]
    exact actual_normalized_parameter_resolvent_constant_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne constant
  · change ContinuousMap.toLp 2 measure ℝ (parameter • actualEnergyContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor
      (parameterEnergySolutionCompletion20261011 (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) parameter parameterAtLeastOne (ContinuousMap.toLp 2 measure ℝ forcing))) = _
    rw [map_smul]
    rfl

theorem actualNormalizedContinuousResolvent_energy_calibration_completion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    actualNormalizedContinuousResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      parameter parameterAtLeastOne
      (actualEnergyContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor forcing) =
    actualEnergyContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor
      (actualNormalizedResolventSolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        parameter parameterAtLeastOne forcing) := by
  change parameter • actualEnergyContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor
    (parameterEnergySolutionCompletion20261011 (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) parameter parameterAtLeastOne
      (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure forcing)) = _
  rw [← map_smul]
  congr 1
  simp only [actualNormalizedResolventSolutionCompletion20261011, normalizedAnchoredResolventSolutionCompletion20261011,
    parameterEnergySolutionCompletion20261011, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, map_smul]

theorem contraction_converges_on_dense_range_completion20261011
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

theorem actualNormalizedContinuousResolvent_uniform_tendsto_completion20261011
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
        (actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
          (parameters index) (parametersAtLeastOne index) forcing)) atTop (𝓝 forcing) := by
  have domainRange := completionEnergyDomain_eq_extension_range
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)
  have denseEmbedding : DenseRange (actualEnergyContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) := by
    change Dense (Set.range (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks))
    exact (congrArg Dense domainRange).mp denseDomain
  apply contraction_converges_on_dense_range_completion20261011
    (fun index => actualNormalizedContinuousResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (parameters index) (parametersAtLeastOne index))
    (fun index => actualNormalizedContinuousResolvent_supnorm_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      (parameters index) (parametersAtLeastOne index)) _ denseEmbedding
  intro potential
  have uniform := actualNormalizedResolventSolution_uniform_tendsto_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    parameters parametersAtLeastOne parametersDiverge potential
  have converted := (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ).symm.continuous.tendsto
    (actualEnergyBoundedEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential)
      |>.comp uniform
  simpa only [actualNormalizedContinuousResolvent_energy_calibration_completion20261011,
    actualEnergyBoundedEmbeddingCompletion20261011, ContinuousLinearMap.comp_apply, Function.comp_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv, Function.comp_def, LinearIsometryEquiv.symm_apply_apply] using converted

end
end IGSIII34.Diffusion



