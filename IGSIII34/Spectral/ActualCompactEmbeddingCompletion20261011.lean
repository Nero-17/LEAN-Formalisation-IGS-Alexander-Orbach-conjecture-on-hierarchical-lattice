import IGSIII34.Spectral.ActualEvaluationCompletion20261011
import IGSIII34.Spectral.CompactEmbedding
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! Actual finite-energy extension embeds compactly into continuous functions
and hence into L² of the mass measure. This is the form compactness step,
before constructing the actual resolvent and its eigenfunctions. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped Topology BoundedContinuousFunction

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]

def actualAnchoredEnergyDomainCompletion20261011
    (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks) : Type :=
  actualEnergyDomain rule p positive belowOne fixedPoint growth value growthPositive marks

local instance actualEmbeddingNormCompletion20261011 :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualEmbeddingUniformCompletion20261011 :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualEmbeddingTopologyCompletion20261011 :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualEmbeddingInnerCompletion20261011 :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

def actualEnergyContinuousEmbeddingCompletion20261011 :
    actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor →L[ℝ]
      C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint
        growth value growthPositive marks), ℝ) :=
  (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks).mkContinuous
    (Real.sqrt (2 * (Metric.diam (Set.univ : Set (UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))) + 1))) (by
      intro potential
      apply (ContinuousMap.norm_le _ (by positivity)).mpr
      intro point
      apply (actual_completion_evaluation_bound rule p positive belowOne fixedPoint growth value
        growthPositive marks anchor point potential).trans
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg potential)
      apply Real.sqrt_le_sqrt
      have bound := Metric.dist_le_diam_of_mem (isCompact_univ.isBounded)
        (Set.mem_univ point) (Set.mem_univ (anchor : UniformSpace.Completion _))
      linarith)

def actualEnergyBoundedEmbeddingCompletion20261011 :
    actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor →L[ℝ]
      (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint
        growth value growthPositive marks) →ᵇ ℝ) :=
  (ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (actualEnergyContinuousEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)

theorem actualEnergyBoundedEmbedding_compact_completion20261011 :
    IsCompactOperator (actualEnergyBoundedEmbeddingCompletion20261011 rule p positive belowOne
      fixedPoint growth value growthPositive marks anchor) := by
  let embedding := actualEnergyBoundedEmbeddingCompletion20261011 rule p positive belowOne fixedPoint
    growth value growthPositive marks anchor
  let family := embedding '' Metric.closedBall 0 1
  have energyBound (potential : actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)
      (member : potential ∈ Metric.closedBall 0 1) :
      limitingEnergy (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks) potential.val ≤ 1 := by
    have normBound : ‖potential‖ ≤ 1 := by simpa using member
    have square := actual_anchored_norm_square rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential
    nlinarith [sq_nonneg (potential.val anchor), norm_nonneg potential]
  have oscillation : ∀ function ∈ family, ∀ first second,
      (function first - function second) ^ 2 ≤ dist first second * (1 : ℝ) := by
    rintro function ⟨potential, member, rfl⟩ first second
    exact (actualEnergyExtension_resistance rule p positive belowOne fixedPoint growth value growthPositive
      marks potential first second).trans
        (mul_le_mul_of_nonneg_left (energyBound potential member) dist_nonneg)
  have compact : IsCompact (closure family) := by
    apply BoundedContinuousFunction.arzela_ascoli (Set.Icc (-‖embedding‖) ‖embedding‖) isCompact_Icc family
    · rintro function point ⟨potential, member, rfl⟩
      have normBound : ‖potential‖ ≤ 1 := by simpa using member
      have bounded : ‖embedding potential‖ ≤ ‖embedding‖ :=
        (embedding.le_opNorm potential).trans (by nlinarith [norm_nonneg embedding])
      have absolute := (BoundedContinuousFunction.norm_coe_le_norm (embedding potential) point).trans bounded
      exact abs_le.mp (by simpa only [Real.norm_eq_abs] using absolute)
    · exact resistance_ball_equicontinuous family (fun _ => 1) (fun _ _ => le_rfl) oscillation
  apply (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image embedding).mpr
  exact ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ zero_lt_one, compact⟩

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

def actualEnergyL2EmbeddingCompletion20261011 :
    actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor →L[ℝ] Lp ℝ 2 measure :=
  (BoundedContinuousFunction.toLp 2 measure ℝ).comp
    (actualEnergyBoundedEmbeddingCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor)

theorem actualEnergyL2Embedding_compact_completion20261011 :
    IsCompactOperator (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive marks anchor measure) :=
  (actualEnergyBoundedEmbedding_compact_completion20261011 rule p positive belowOne fixedPoint
    growth value growthPositive marks anchor).clm_comp (BoundedContinuousFunction.toLp 2 measure ℝ)

theorem actualEnergyL2Embedding_injective_completion20261011 [measure.IsOpenPosMeasure] :
    Function.Injective (actualEnergyL2EmbeddingCompletion20261011 rule p positive belowOne fixedPoint
      growth value growthPositive marks anchor measure) :=
  (BoundedContinuousFunction.toLp_injective measure).comp
    ((ContinuousMap.linearIsometryBoundedOfCompact _ ℝ ℝ).injective.comp
      (actualEnergyExtensionLinear_injective rule p positive belowOne fixedPoint growth value growthPositive marks))

end
end IGSIII34.Spectral
