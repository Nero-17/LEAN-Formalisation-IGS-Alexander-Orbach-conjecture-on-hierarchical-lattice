import IGSIII34.Diffusion.ActualScaledContinuousResolventCompletion
import IGSIII34.Spectral.ScalarSpeedMeasureCompletion

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

local instance ActualScalarSpeedSolutionCompletionNorm :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualScalarSpeedSolutionCompletionUniform :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance ActualScalarSpeedSolutionCompletionTopology :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ActualScalarSpeedSolutionCompletionInner :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualScalarSpeedSolutionCompletionComplete :
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

/-! Scaling the speed measure of the actual retained electrical form.
The solution below is constructed by the established coercive resolvent;
its variational equation uses C times the same physical Perron measure. -/

theorem actualParameterResolventBilinear_integral_pairing_completion
    (parameter : ℝ)
    (first second : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    parameterAnchoredResolventBilinearCompletion
      (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) parameter first second =
      limitingPairing (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) first.val second.val +
      parameter * ∫ point,
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks first point *
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks second point ∂measure := by
  have massPairing : inner ℝ
      (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure first)
      (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure second) =
      ∫ point,
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks first point *
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks second point ∂measure := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [actualEnergyL2Embedding_representative_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure first,
      actualEnergyL2Embedding_representative_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure second]
      with point firstEquality secondEquality
    rw [firstEquality, secondEquality]
    change actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks second point *
      actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks first point = _
    ring
  rw [parameterAnchoredResolventBilinear_apply_completion,
    actualAnchoredInner_energy_pairing_completion,
    actualAnchorEvaluation_apply_completion,
    actualAnchorEvaluation_apply_completion, massPairing]
  ring

theorem actualContinuousEnergySolution_integral_pairing_completion
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (test : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    limitingPairing (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
      (actualContinuousEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        parameter parameterAtLeastOne forcing).val test.val +
      parameter * ∫ point,
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
          (actualContinuousEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
            parameter parameterAtLeastOne forcing) point *
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks test point ∂measure =
      ∫ point, forcing point * actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks test point ∂measure := by
  have variational := actualContinuousEnergySolution_variational_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    parameter parameterAtLeastOne forcing test
  rw [actualParameterResolventBilinear_integral_pairing_completion,
    actualContinuousForcingDual_integral_completion] at variational
  exact variational

def actualScalarSpeedEnergySolutionCompletion
    (constant parameter : ℝ) (coerciveRange : 1 ≤ parameter * constant)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor :=
  actualContinuousEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    (parameter * constant) coerciveRange (constant • forcing)

theorem actualScalarSpeedEnergySolution_variational_completion
    (constant : ℝ) (constantPositive : 0 < constant)
    (parameter : ℝ) (coerciveRange : 1 ≤ parameter * constant)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (test : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    limitingPairing (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
      (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
      (actualScalarSpeedEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        constant parameter coerciveRange forcing).val test.val +
      parameter * ∫ point,
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
          (actualScalarSpeedEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
            constant parameter coerciveRange forcing) point *
        actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks test point
        ∂scalarSpeedMeasureCompletion measure constant =
      ∫ point, forcing point * actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks test point
        ∂scalarSpeedMeasureCompletion measure constant := by
  apply (scalarSpeedMeasure_variational_equivalence_completion measure constant constantPositive _ parameter _ _ _).mpr
  have variational := actualContinuousEnergySolution_integral_pairing_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    (parameter * constant) coerciveRange (constant • forcing) test
  simpa only [actualScalarSpeedEnergySolutionCompletion, ContinuousMap.smul_apply,
    smul_eq_mul, mul_assoc, integral_const_mul] using variational

theorem actualScalarSpeedEnergySolution_extension_completion
    (constant parameter : ℝ) (coerciveRange : 1 ≤ parameter * constant)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (actualScalarSpeedEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        constant parameter coerciveRange forcing) = constant •
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (actualContinuousEnergySolutionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (parameter * constant) coerciveRange forcing) :=
  actualContinuousEnergySolution_scaled_forcing_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    (parameter * constant) coerciveRange constant forcing

end
end IGSIII34.Diffusion