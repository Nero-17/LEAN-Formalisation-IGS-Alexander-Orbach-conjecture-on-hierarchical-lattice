import IGSIII34.Spectral.CompactEigenbasisCompletion
import IGSIII34.Spectral.ResolventEigenvaluesCompletion
import IGSIII34.Spectral.ActualResolventCompletion
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

local instance actualSpectrumNormCompletion :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualSpectrumUniformCompletion :
    UniformSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualSpectrumTopologyCompletion :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualSpectrumInnerCompletion :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance actualSpectrumCompleteCompletion :
    CompleteSpace (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure]

theorem actualResolvent_energy_nonnegative_completion
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :
    0 ≤ ‖potential‖ ^ 2 -
      actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential ^ 2 := by
  rw [actual_anchored_norm_square rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential,
    actualAnchorEvaluation_apply_completion]
  have nonnegative := limitingEnergy_nonnegative
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)
    potential.property
  linarith

theorem actualL2Resolvent_norm_le_completion (forcing : Lp ℝ 2 measure) :
    ‖actualL2ResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure forcing‖ ≤ ‖forcing‖ :=
  anchoredL2Resolvent_norm_le_completion _ _ _
    (actualResolvent_energy_nonnegative_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) forcing

theorem exists_actual_resolvent_eigenbasis_completion [measure.WeaklyRegular]
    (denseDomain : Dense
      (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
        (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier) :
    ∃ Index : Type, ∃ basis : HilbertBasis Index ℝ (Lp ℝ 2 measure),
      ∃ eigenvalues : Index → ℝ,
      Countable Index ∧ (∀ index, 0 < eigenvalues index ∧ eigenvalues index ≤ 1) ∧
      (∀ index, actualL2ResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (basis index) = eigenvalues index • basis index) ∧
      (∀ index, 0 ≤ (eigenvalues index)⁻¹ - 1) ∧
      Tendsto (fun index => (eigenvalues index)⁻¹ - 1) cofinite atTop := by
  let operator := actualL2ResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
  have compact := actualL2Resolvent_compact_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
  obtain ⟨Index, basis, eigenvalues, eigenvectors⟩ :=
    exists_compact_selfadjoint_Hilbert_eigenbasis_completion operator compact
      (actualL2Resolvent_symmetric_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
  have positive := compact_positive_injective_eigenvalues_completion operator
    (anchoredL2Resolvent_nonnegative_completion _ _ _)
    (actualL2Resolvent_kernel_zero_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure denseDomain)
    (actualL2Resolvent_norm_le_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)
    basis basis.orthonormal eigenvalues eigenvectors
  have countable := countable_compact_positive_eigenfamily_completion operator compact
    basis basis.orthonormal eigenvalues (fun index => (positive index).1) eigenvectors
  have diverges := compact_generator_eigenvalues_diverge_completion operator compact
    basis basis.orthonormal eigenvalues (fun index => (positive index).1)
    (fun index => (positive index).2) eigenvectors
  exact ⟨Index, basis, eigenvalues, countable, positive, eigenvectors, diverges.1, diverges.2⟩

end
end IGSIII34.Spectral

