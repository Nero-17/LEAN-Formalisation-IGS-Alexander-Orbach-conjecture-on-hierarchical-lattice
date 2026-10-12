import IGSIII34.Spectral.ActualCompactEmbeddingCompletion
import IGSIII34.Spectral.AnchoredResolventCompletion
import IGSIII34.Forms.L2ClosednessCompletion
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

local instance actualResolventNormCompletion :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualResolventUniformCompletion :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualResolventTopologyCompletion :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualResolventInnerCompletion :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualResolventCompleteCompletion :
    CompleteSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

def actualAnchorEvaluationCompletion :
    StrongDual ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualCompletionEvaluation rule p positive belowOne fixedPoint growth value growthPositive marks anchor anchor

theorem actualAnchorEvaluation_apply_completion
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential =
      potential.val anchor :=
  completionExtension_coe
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)
    potential anchor

theorem actualEnergyL2Embedding_norm_square_completion
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    ‖actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure potential‖ ^ 2 =
      ∫ point, actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential point ^ 2 ∂measure := by
  have representative :
      (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure potential) =ᵐ[measure]
        (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks potential) :=
    BoundedContinuousFunction.coeFn_toLp 2 measure ℝ
      (actualEnergyBoundedEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential)
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [representative] with point equality
  rw [equality]
  simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

theorem actualResolventBilinear_self_completion
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    anchoredResolventBilinearCompletion
      (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) potential potential =
        completionFormSquare (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
          (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
          (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks) measure potential := by
  rw [anchoredResolventBilinear_self_completion,
    actualAnchorEvaluation_apply_completion,
    actualEnergyL2Embedding_norm_square_completion,
    actual_anchored_norm_square rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential]
  simp only [completionFormSquare, actualEnergyExtensionLinear, completionExtensionLinear]
  ring
  rfl

theorem actualResolventBilinear_coercive_completion :
    IsCoercive (anchoredResolventBilinearCompletion
      (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
      (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor)) := by
  apply anchoredResolventBilinear_coercive_completion _ _
    (2 * Metric.diam (Set.univ : Set (UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))) + 3) (by positivity)
  intro potential
  have comparison := anchoredSquare_le_completionFormSquare (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)
    measure anchor (Metric.diam Set.univ) Metric.diam_nonneg
    (fun point => Metric.dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ _) (Set.mem_univ _))
    potential (completionExtension_square_integrable (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) _ _ _ measure potential)
  have square := actual_anchored_norm_square rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential
  have form := actualResolventBilinear_self_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure potential
  rw [anchoredResolventBilinear_self_completion] at form
  rw [form]
  simpa only [anchoredSquare, ← square] using comparison

def actualL2ResolventCompletion : Lp ℝ 2 measure →L[ℝ] Lp ℝ 2 measure :=
  anchoredL2ResolventCompletion
    (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
    (actualResolventBilinear_coercive_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)

theorem actualL2Resolvent_compact_completion :
    IsCompactOperator (actualL2ResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) :=
  anchoredL2Resolvent_compact_completion _ _ _
    (actualEnergyL2Embedding_compact_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)

theorem actualL2Resolvent_symmetric_completion :
    (actualL2ResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure).toLinearMap.IsSymmetric :=
  anchoredL2Resolvent_symmetric_completion _ _ _

theorem actualEnergyL2Embedding_dense_completion [measure.WeaklyRegular]
    (denseDomain : Dense
      (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier) :
    DenseRange (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure) := by
  have rangeEquality := completionEnergyDomain_eq_extension_range (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks)
  have denseExtension : DenseRange (actualEnergyContinuousEmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) := by
    change Dense (Set.range (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks))
    exact (congrArg Dense rangeEquality).mp denseDomain
  have combined := (ContinuousMap.toLp_denseRange ℝ measure ℝ (p := 2) (by norm_num)).comp
    denseExtension (ContinuousMap.toLp 2 measure ℝ).continuous
  exact combined

theorem actualL2Resolvent_kernel_zero_completion [measure.WeaklyRegular]
    (denseDomain : Dense
      (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier)
    (forcing : Lp ℝ 2 measure)
    (zero : actualL2ResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure forcing = 0) :
    forcing = 0 :=
  anchoredL2Resolvent_kernel_zero_completion _ _ _
    (actualEnergyL2Embedding_dense_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure denseDomain)
    forcing zero

end
end IGSIII34.Spectral
