import IGSIII34.Diffusion.ActualWholeContinuousResolventCompletion20261011
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

local instance ActualScaledContinuousResolventCompletion20261011Norm :
    NormedAddCommGroup (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualScaledContinuousResolventCompletion20261011Uniform :
    UniformSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace
local instance ActualScaledContinuousResolventCompletion20261011Topology :
    TopologicalSpace (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  (actualAnchoredNormedAddCommGroup rule p positive belowOne fixedPoint growth value growthPositive marks anchor).toMetricSpace.toUniformSpace.toTopologicalSpace
local instance ActualScaledContinuousResolventCompletion20261011Inner :
    InnerProductSpace ℝ (actualAnchoredEnergyDomainCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor) :=
  actualAnchoredInnerProductSpace rule p positive belowOne fixedPoint growth value growthPositive marks anchor
local instance ActualScaledContinuousResolventCompletion20261011Complete :
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

theorem actualContinuousEnergySolution_scaled_forcing_completion20261011
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (scalar : ℝ)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        parameter parameterAtLeastOne (scalar • forcing)) = scalar •
    actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        parameter parameterAtLeastOne forcing) := by
  simp only [actualContinuousEnergySolutionCompletion20261011, actualContinuousForcingL2Completion20261011, map_smul]

variable (denseDomain : Dense
  (completionEnergyDomain (Carrier := ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive marks)
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value marks)
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks)).carrier)

include denseDomain in
theorem actualContinuousEnergySolution_scaled_uniform_tendsto_completion20261011
    (parameters : ℕ → ℝ) (parametersAtLeastOne : ∀ index, 1 ≤ parameters index)
    (parametersDiverge : Tendsto parameters atTop atTop)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ)) :
    Tendsto (fun index => actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (parameters index) (parametersAtLeastOne index) (parameters index • forcing))) atTop (𝓝 forcing) := by
  simpa only [actualContinuousEnergySolution_scaled_forcing_completion20261011] using
    actualNormalizedContinuousResolvent_uniform_tendsto_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      denseDomain parameters parametersAtLeastOne parametersDiverge forcing

include denseDomain in
theorem actualContinuousEnergySolution_scaled_uniform_values_completion20261011
    (parameters : ℕ → ℝ) (parametersAtLeastOne : ∀ index, 1 ≤ parameters index)
    (parametersDiverge : Tendsto parameters atTop atTop)
    (forcing : C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (error : ℝ) (errorPositive : 0 < error) :
    ∀ᶠ index in atTop, ∀ point,
      ‖actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
        (actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
          (parameters index) (parametersAtLeastOne index) (parameters index • forcing)) point - forcing point‖ < error := by
  have uniform := actualContinuousEnergySolution_scaled_uniform_tendsto_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
    denseDomain parameters parametersAtLeastOne parametersDiverge forcing
  filter_upwards [uniform.eventually (Metric.ball_mem_nhds forcing errorPositive)] with index close
  intro point
  have bound := ContinuousMap.norm_coe_le_norm
    (actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
      (actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
        (parameters index) (parametersAtLeastOne index) (parameters index • forcing)) - forcing) point
  exact bound.trans_lt (by simpa only [Metric.mem_ball, dist_eq_norm] using close)

include denseDomain in
theorem actualContinuousEnergySolution_finite_scaled_uniform_values_completion20261011
    {Label : Type*} [Finite Label]
    (parameters : ℕ → ℝ) (parametersAtLeastOne : ∀ index, 1 ≤ parameters index)
    (parametersDiverge : Tendsto parameters atTop atTop)
    (forcing : Label → C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive marks), ℝ))
    (error : ℝ) (errorPositive : 0 < error) :
    ∀ᶠ index in atTop, ∀ label point,
      ‖actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive marks
        (actualContinuousEnergySolutionCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
          (parameters index) (parametersAtLeastOne index) (parameters index • forcing label)) point - forcing label point‖ < error :=
  Filter.eventually_all.mpr (fun label =>
    actualContinuousEnergySolution_scaled_uniform_values_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks anchor measure
      denseDomain parameters parametersAtLeastOne parametersDiverge (forcing label) error errorPositive)

end
end IGSIII34.Diffusion

