import IGSIII34.Spectral.ActualSpectralDataCompletion
import IGSIII34.Spectral.ClockSpectralExponentCompletion
import Mathlib.Tactic.FunProp
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution MeasureTheory Filter InnerProductSpace
open scoped Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
  [CompactSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]

local instance : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance : UniformSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance : CompleteSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor

variable [MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  [BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks))]
  (measure : Measure (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)))
  [IsProbabilityMeasure measure] [measure.IsOpenPosMeasure]
  (data : ActualSpectralDataCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure)

theorem actualSpectralData_diagonal_measurable_completion
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    Measurable (fun time => actualSpectralHeatKernelCompletion rule p positive belowOne fixedPoint growth value growthPositive
      marks anchor measure data time point point) := by
  letI := data.countable
  change Measurable (fun time : ℝ => ∑' index,
    Real.exp (-time * ((data.resolventEigenvalues index)⁻¹ - 1)) *
      actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index point *
      actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure data index point)
  apply Measurable.tsum
  intro index
  fun_prop

include data anchor in
theorem actualSpectralData_resolvent_antitone_completion
    (point : UniformSpace.Completion
      (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)) :
    AntitoneOn (fun parameter => actualDiagonalVariationalResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive
      marks measure parameter point) (Set.Ici 1) := by
  intro first firstAtLeastOne second secondAtLeastOne ordered
  change 1 ≤ first at firstAtLeastOne
  change 1 ≤ second at secondAtLeastOne
  dsimp only at ⊢
  have firstSum := actualSpectralData_weighted_sum_completion rule p positive belowOne fixedPoint growth value growthPositive
    marks anchor measure data point first firstAtLeastOne
  have secondSum := actualSpectralData_weighted_sum_completion rule p positive belowOne fixedPoint growth value growthPositive
    marks anchor measure data point second secondAtLeastOne
  rw [← firstSum.tsum_eq, ← secondSum.tsum_eq]
  apply secondSum.summable.tsum_le_tsum _ firstSum.summable
  intro index
  exact div_le_div_of_nonneg_left (sq_nonneg _)
    (by linarith [data.generatorNonnegative index]) (by linarith)

include data anchor in
theorem actualSpectralData_resolvent_point_measurable_completion
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) :
    Measurable (fun point => actualDiagonalVariationalResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive
      marks measure parameter point) := by
  letI := data.countable
  have equality : (fun point => actualDiagonalVariationalResolventCompletion rule p positive belowOne fixedPoint growth value growthPositive
      marks measure parameter point) =
      (fun point => ∑' index, actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive
        marks anchor measure data index point^2 / (parameter + ((data.resolventEigenvalues index)⁻¹ - 1))) := by
    funext point
    exact (actualSpectralData_weighted_sum_completion rule p positive belowOne fixedPoint growth value growthPositive
      marks anchor measure data point parameter parameterAtLeastOne).tsum_eq.symm
  rw [equality]
  apply Measurable.tsum
  intro index
  exact (((actualSpectralEigenfunctionsCompletion rule p positive belowOne fixedPoint growth value growthPositive
    marks anchor measure data index).continuous.measurable).pow_const 2).div_const _

end
end IGSIII34.Spectral
