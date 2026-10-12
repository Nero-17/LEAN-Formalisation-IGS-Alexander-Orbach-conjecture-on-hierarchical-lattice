import IGSIII34.Spectral.ActualHarmonicAnchoredCompletion
import IGSIII34.Spectral.ActualDiagonalResolventCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000
namespace IGSIII34.Spectral
noncomputable section
open IGSIII34.Diffusion
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
  [CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))]

local instance actualHarmonicParameterNormCompletion : NormedAddCommGroup
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor
local instance actualHarmonicParameterUniformCompletion : UniformSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualHarmonicParameterNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance actualHarmonicParameterTopologyCompletion : TopologicalSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  (actualHarmonicParameterNormCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance actualHarmonicParameterInnerCompletion : InnerProductSpace ℝ
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor

local instance actualHarmonicParameterCompleteCompletion : CompleteSpace
    (actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :=
  actual_anchored_completeSpace rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor


variable [MeasurableSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))]
  [BorelSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))]
  (measure : Measure (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))))
  [IsProbabilityMeasure measure]

theorem actual_harmonic_interpolation_parameter_bilinear_tendsto_completion
    (parameter : ℝ)
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :
    Tendsto (fun depth => parameterAnchoredResolventBilinearCompletion
      (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure)
      (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) parameter
      (potential - actualAnchoredHarmonicInterpolationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor depth potential)
      (potential - actualAnchoredHarmonicInterpolationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor depth potential))
      atTop (𝓝 0) := by
  have residual : Tendsto (fun depth => potential - actualAnchoredHarmonicInterpolationCompletion
      rule p positive belowOne fixedPoint growth value growthPositive marks anchor depth potential) atTop (𝓝 0) := by
    have constant : Tendsto (fun _ : ℕ => potential) atTop (𝓝 potential) := tendsto_const_nhds
    simpa only [sub_self] using constant.sub
      (actual_harmonic_interpolation_anchored_tendsto_completion rule p positive belowOne fixedPoint growth value growthPositive marks anchor potential)
  have diagonalContinuous :=
    (parameterAnchoredResolventBilinearCompletion
      (actualEnergyL2EmbeddingCompletion rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor measure)
      (actualAnchorEvaluationCompletion rule p positive belowOne fixedPoint growth value growthPositive
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) parameter).continuous.clm_apply continuous_id
  convert (diagonalContinuous.tendsto 0).comp residual using 1 <;> simp only [map_zero, zero_apply, id_eq]
  rfl

theorem actual_harmonic_interpolation_parameter_energy_tendsto_completion
    (parameter : ℝ)
    (potential : actualAnchoredEnergyDomainCompletion rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks) anchor) :
    Tendsto (fun depth =>
      limitingEnergy
        (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (actualEnergyConductance rule p positive belowOne fixedPoint growth value
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
        (fun point => potential.val point - actualHarmonicInterpolation rule p positive belowOne fixedPoint growth value growthPositive marks depth potential.val point) +
      parameter * ∫ point,
        (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)
          (potential - actualAnchoredHarmonicInterpolationCompletion rule p positive belowOne fixedPoint growth value growthPositive marks anchor depth potential) point)^2 ∂measure)
      atTop (𝓝 0) := by
  have limit := actual_harmonic_interpolation_parameter_bilinear_tendsto_completion
    rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure parameter potential
  simp only [actualParameterResolventBilinear_self_completion] at limit
  convert limit using 1
  funext depth
  rfl

end
end IGSIII34.Spectral
