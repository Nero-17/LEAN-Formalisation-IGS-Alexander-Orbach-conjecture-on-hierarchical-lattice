import IGSIII34.Spectral.ActualResolventPositivityCompletion20261011

/-! The actual parameter resolvent fixes the appropriate constant forcing.
Together with proved positivity this yields its pointwise maximum principle. -/
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
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

local instance ActualResolventConservationCompletion20261011Norm :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualResolventConservationCompletion20261011Uniform :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance ActualResolventConservationCompletion20261011Topology :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ActualResolventConservationCompletion20261011Inner :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualResolventConservationCompletion20261011Complete :
    CompleteSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

def actualEnergyConstantCompletion20261011 (constant : ℝ) :
    actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor :=
  ⟨fun _ => constant, ⟨0, by
    rintro energy ⟨depth, rfl⟩
    exact (finiteEnergy_constant
      (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks depth)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks depth) constant).le⟩⟩

theorem actualEnergyConstant_extension_completion20261011 (constant : ℝ)
    (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant) point = constant := by
  have equality := (UniformSpace.Completion.denseRange_coe (α := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)).equalizer
    (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant)).continuous
    continuous_const (by
      funext vertex
      change completionExtension
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant)
        (@UniformSpace.Completion.coe'
          (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
          inferInstance vertex) = constant
      exact completionExtension_coe _ _ _
        (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks) _ vertex)
  exact congrFun equality point

theorem actualEnergyConstant_pairing_zero_completion20261011 (constant : ℝ)
    (potential : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    limitingPairing (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
      (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant).val potential.val = 0 := by
  apply tendsto_nhds_unique
    (tracePairing_tendsto _ _
      (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actual_traceEnergy_monotone rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant).property potential.property)
  simpa [tracePairing, finitePairing, actualEnergyConstantCompletion20261011] using
    (tendsto_const_nhds : Tendsto (fun _depth : ℕ => (0 : ℝ)) atTop (𝓝 0))

theorem actual_parameter_resolvent_constant_completion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (constant : ℝ) :
    parameterEnergySolutionCompletion20261011
      (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
      (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      parameter parameterAtLeastOne
      (parameter • actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant)) =
    actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant := by
  apply coercive_bilinear_unique_completion20261011 _
    (parameterAnchoredResolventBilinear_coercive_completion20261011 _ _
      (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      parameter parameterAtLeastOne)
  intro test
  rw [parameterEnergySolution_variational_completion20261011,
    parameterAnchoredResolventBilinear_apply_completion20261011,
    actualAnchoredInner_energy_pairing_completion20261011,
    actualAnchorEvaluation_apply_completion20261011,
    actualAnchorEvaluation_apply_completion20261011,
    actualEnergyConstant_pairing_zero_completion20261011, real_inner_smul_left]
  ring

theorem actual_parameter_resolvent_upper_bound_completion20261011 [measure.IsOpenPosMeasure]
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : Lp ℝ 2 measure)
    (constant : ℝ) (forcingUpper : ∀ᵐ point ∂measure, forcing point ≤ parameter * constant)
    (point : UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (parameterEnergySolutionCompletion20261011
        (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
        (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
        parameter parameterAtLeastOne forcing) point ≤ constant := by
  let constantPotential := actualEnergyConstantCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant
  let constantL2 := actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure constantPotential
  have constantRepresentative : ∀ᵐ vertex ∂measure, constantL2 vertex = constant := by
    filter_upwards [actualEnergyL2Embedding_representative_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure constantPotential] with vertex representative
    exact representative.trans (actualEnergyConstant_extension_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor constant vertex)
  have differenceNonnegative : ∀ᵐ vertex ∂measure, 0 ≤ (parameter • constantL2 - forcing) vertex := by
    filter_upwards [Lp.coeFn_sub (parameter • constantL2) forcing, Lp.coeFn_smul parameter constantL2, constantRepresentative, forcingUpper]
      with vertex subtraction scalar constantAt upper
    rw [subtraction, Pi.sub_apply, scalar, Pi.smul_apply, smul_eq_mul, constantAt]
    exact sub_nonneg.mpr upper
  have positivity := actual_parameter_resolvent_nonnegative_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    parameter parameterAtLeastOne (parameter • constantL2 - forcing) differenceNonnegative point
  rw [map_sub, actual_parameter_resolvent_constant_completion20261011,
    map_sub, ContinuousMap.sub_apply, actualEnergyConstant_extension_completion20261011] at positivity
  linarith

end
end IGSIII34.Spectral



