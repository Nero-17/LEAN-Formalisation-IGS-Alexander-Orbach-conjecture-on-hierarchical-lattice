import IGSIII34.Spectral.ActualSpectralDataCompletion20261011
import IGSIII34.Spectral.PositiveParameterHilbert20261011
import IGSIII34.Spectral.ParameterFormHilbertCompletion20261011
import IGSIII34.Spectral.HeatLaplaceIdentityCompletion20261011
import IGSIII34.Spectral.ActualEigenbasisCompletion20261011
import IGSIII34.Spectral.AnchoredFormSpectrumCompletion20261011
import IGSIII34.Spectral.FormEigenvectorsImageCompletion20261011
import IGSIII34.Spectral.ContinuousSpectralKernelCompletion20261011
import IGSIII34.Spectral.CompactEigenbasisCompletion20261011
import IGSIII34.Spectral.ResolventEigenvaluesCompletion20261011
import IGSIII34.Spectral.ActualResolventCompletion20261011
import IGSIII34.Spectral.ActualCompactEmbeddingCompletion20261011
import IGSIII34.Spectral.AnchoredResolventCompletion20261011
import IGSIII34.Forms.L2ClosednessCompletion20261011
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! The actual compact L² resolvent is constructed by Lax-Milgram from the
proved electrical energy. The mass-measure input is kept explicit until the
actual electrical boundary pushforward is assembled. -/
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

local instance actualPositiveDiagonalNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualPositiveDiagonalUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualPositiveDiagonalTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualPositiveDiagonalInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualPositiveDiagonalCompleteCompletion20261011 :
    CompleteSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]


open IGSIII34.Diffusion

theorem actual_positive_parameter_resolvent_coercive_completion20261011
    (parameter : ℝ) (parameterPositive : 0 < parameter) :
    IsCoercive (parameterAnchoredResolventBilinearCompletion20261011
      (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
      parameter) := by
  obtain ⟨coefficient, coefficientPositive, lower⟩ :=
    (show IsCoercive _ from actualResolventBilinear_coercive_completion20261011
      rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
  refine ⟨min 1 parameter * coefficient, mul_pos (lt_min zero_lt_one parameterPositive) coefficientPositive, ?_⟩
  intro potential
  have scaled := mul_le_mul_of_nonneg_left (lower potential) (lt_min zero_lt_one parameterPositive).le
  have energyNonnegative := limitingEnergy_nonnegative
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    potential.property
  have massNonnegative : 0 ≤ ∫ point, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point ^ 2 ∂measure :=
    integral_nonneg (fun _ => sq_nonneg _)
  have energyRemainder := mul_nonneg (sub_nonneg.mpr (min_le_left (1 : ℝ) parameter)) energyNonnegative
  have massRemainder := mul_nonneg (sub_nonneg.mpr (min_le_right (1 : ℝ) parameter)) massNonnegative
  rw [anchoredResolventBilinear_apply_completion20261011,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    actualAnchorEvaluation_apply_completion20261011,
    actualEnergyL2Embedding_norm_square_completion20261011,
    actual_anchored_norm_square rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential] at scaled
  rw [actualParameterResolventBilinear_self_completion20261011]
  nlinarith [scaled, energyRemainder, massRemainder]

theorem actual_completion_diagonal_local_upper_positive_completion20261011
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (cell : Set (UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
    (cellMeasurable : MeasurableSet cell) (diameter : ℝ) (diameterNonnegative : 0 ≤ diameter)
    (diameterBound : ∀ other ∈ cell, dist point other ≤ diameter)
    (massPositive : 0 < measure.real cell) :
    actualDiagonalVariationalResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure parameter point ≤
      2 * max (1 / (parameter * measure.real cell)) diameter := by
  apply csSup_le (Set.range_nonempty _)
  rintro result ⟨potential, rfl⟩
  exact actual_local_completion_resolvent_evaluation_bound_completion20261011 rule p positive belowOne fixedPoint growth value
    growthPositive marks measure point cell cellMeasurable diameter diameterNonnegative diameterBound massPositive
    parameter parameterPositive potential

variable [measure.IsOpenPosMeasure]
  (data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)

theorem actualSpectralData_positive_weighted_sum_completion20261011
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (parameter : ℝ) (parameterPositive : 0 < parameter) :
    HasSum (fun index => actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index point ^ 2 /
      (parameter + ((data.resolventEigenvalues index)⁻¹ - 1)))
      (actualDiagonalVariationalResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure parameter point) := by
  have denominatorsPositive : ∀ index, 0 < 1 + (parameter - 1) * data.resolventEigenvalues index := by
    intro index
    have positiveProduct := mul_pos parameterPositive (data.eigenvaluesPositive index)
    have atMostOne := data.atMostOne index
    nlinarith
  have identity := PositiveParameter.parameterFormEvaluation_spectral_identity_completion20261011
    (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualAnchorEvaluationCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    parameter (actual_positive_parameter_resolvent_coercive_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure parameter parameterPositive)
    (actualEnergyL2Embedding_injective_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    data.basis data.resolventEigenvalues data.eigenvaluesPositive denominatorsPositive data.eigenvectors
    (continuousFormEvaluationCompletion20261011
      (actualEnergyContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) point)
  convert identity using 1 <;> simp only [actualParameterResolventBilinear_self_completion20261011,
    actualContinuousFormEvaluation_apply_completion20261011, add_sub_assoc,
    actualDiagonalVariationalResolventCompletion20261011, actualSpectralEigenfunctionsCompletion20261011,
    actualContinuousEigenfunctions_evaluation_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      data.basis data.resolventEigenvalues data.eigenvaluesPositive data.eigenvectors] <;> rfl

theorem actualSpectralData_positive_laplace_variational_completion20261011
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))
    (parameter : ℝ) (parameterPositive : 0 < parameter) :
    diagonalLaplace (fun time => actualSpectralHeatKernelCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data time point point) parameter =
      actualDiagonalVariationalResolventCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks measure parameter point := by
  letI := data.countable
  have identity := indexed_spectral_heat_diagonal_laplace_completion20261011
    (fun index => (data.resolventEigenvalues index)⁻¹ - 1)
    (fun index => actualSpectralEigenfunctionsCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index)
    data.generatorNonnegative parameter parameterPositive point
    (actualSpectralData_positive_weighted_sum_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data point parameter parameterPositive).summable
  exact identity.trans (actualSpectralData_positive_weighted_sum_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data point parameter parameterPositive).tsum_eq

end
end IGSIII34.Spectral
