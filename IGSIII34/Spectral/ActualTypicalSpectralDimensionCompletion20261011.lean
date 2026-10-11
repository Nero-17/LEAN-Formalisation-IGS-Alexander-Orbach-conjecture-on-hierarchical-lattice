import IGSIII34.Spectral.ActualDiagonalClockLowerCompletion20261011
import IGSIII34.Spectral.ActualDiagonalClockUpperCompletion20261011
import IGSIII34.Spectral.ActualSpectralPointAnalysisCompletion20261011
import IGSIII34.Spectral.ClockTauberianCompletion20261011
import IGSIII34.Spectral.RationalClockPushforwardCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4500000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms Resistance
open MeasureTheory Filter Matrix
open scoped BigOperators _root_.Topology

/-- The actual heat kernel has the claimed mass-typical spectral dimension.
The only objects supplied are the already constructed natural resistance,
actual mass ratios, boundary realization and actual resolvent eigenbasis;
no heat or resolvent exponent estimate is assumed. -/
theorem ae_actual_typical_spectral_dimension_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion20261011 rule p positive belowOne fixedPoint)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint)
    (weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks)))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ (typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) marks),
      ∀ (compactness : CompactSpace (UniformSpace.Completion
        (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩)))),
      letI := compactness
      ∀ (boundaryLaw : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
        (probability : IsProbabilityMeasure boundaryLaw)
        (atoms : ∀ depth word, boundaryLaw {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks))
        (retainedPaths : ∀ᵐ path ∂boundaryLaw, ∀ depth,
          Fin.init (path (depth + 1)) = path depth ∧ retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive),
      ∀ (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
        ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩)
        (realizationMeasurable : Measurable realization)
        (convergence : ∀ᵐ path ∂boundaryLaw, Tendsto (fun depth =>
          actualElectricalComponentWordPoint rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) marks typical.1.1 depth (path (depth + 1)))
          atTop (𝓝 (realization path)))
        (massProbability : IsProbabilityMeasure (boundaryLaw.map realization))
        (fullSupport : (boundaryLaw.map realization).IsOpenPosMeasure),
      letI := massProbability
      letI := fullSupport
      ∀ (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) ⟨marks, typical⟩))
        (data : ActualSpectralDataCompletion20261011 rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩) anchor (boundaryLaw.map realization)),
      ∀ᵐ point ∂boundaryLaw.map realization,
        Tendsto (fun time => -2 * Real.log (actualSpectralHeatKernelCompletion20261011
          rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field)
          (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩) anchor (boundaryLaw.map realization) data time point point) / Real.log time)
          (𝓝[>] 0) (𝓝 (2 * Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
            Real.log (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth))) := by
  classical
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have radiusAboveOne : 1 < radius :=
    ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  have growthPositive := zero_lt_one.trans natural.aboveOne
  have clockAboveOne : 1 < radius * natural.growth := by
    nlinarith [mul_pos (sub_pos.mpr radiusAboveOne) (sub_pos.mpr natural.aboveOne)]
  filter_upwards [actual_diagonal_resolvent_clock_lower_completion20261011 rule classicalRule p positive belowOne fixedPoint
      natural continuation weight actualRatios nonnegative,
    actual_diagonal_resolvent_clock_upper_completion20261011 rule classicalRule p positive belowOne fixedPoint natural weight actualRatios]
      with marks lower upper
  intro typical compactness
  letI := compactness
  intro boundaryLaw probability atoms retainedPaths realization realizationMeasurable convergence massProbability fullSupport
  letI := probability
  letI := massProbability
  letI := fullSupport
  intro anchor data
  let diagonal (depth : ℕ) (point : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) growthPositive ⟨marks, typical.1.1⟩) :=
    actualDiagonalVariationalResolventCompletion20261011 rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩)
      (boundaryLaw.map realization) ((radius * natural.growth)^depth) point
  have paths : ∀ᵐ path ∂boundaryLaw, rationalClockBoundsCompletion20261011 diagonal natural.growth (realization path) := by
    filter_upwards [lower typical compactness anchor boundaryLaw probability atoms retainedPaths realization realizationMeasurable convergence fullSupport,
      upper typical compactness boundaryLaw probability atoms retainedPaths realization realizationMeasurable convergence]
      with path lower upper
    intro tolerance greater
    exact (lower (tolerance : ℝ) greater).and (upper (tolerance : ℝ) greater)
  have pointMeasurable (depth : ℕ) : Measurable (diagonal depth) :=
    actualSpectralData_resolvent_point_measurable_completion20261011 rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩)
      anchor (boundaryLaw.map realization) data ((radius * natural.growth)^depth) (one_le_pow₀ clockAboveOne.le)
  have points := rational_clock_bounds_pushforward_completion20261011 boundaryLaw realization realizationMeasurable diagonal natural.growth pointMeasurable paths
  filter_upwards [points] with point bounds
  let exponent := Real.log radius / Real.log (radius * natural.growth)
  have interval := clock_spectral_exponent_interval_completion20261011 radius natural.growth radiusAboveOne natural.aboveOne
  have exponentIdentity : (radius * natural.growth)^(exponent - 1) = natural.growth⁻¹ := by
    rw [clock_spectral_exponent_difference_completion20261011 radius natural.growth radiusAboveOne natural.aboveOne]
    exact clock_resistance_exponent_identity_completion20261011 radius natural.growth radiusAboveOne natural.aboveOne
  have result := spectral_dimension_from_true_clock_bounds_completion20261011
    (fun time => actualSpectralHeatKernelCompletion20261011 rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩)
      anchor (boundaryLaw.map realization) data time point point)
    (fun parameter => actualDiagonalVariationalResolventCompletion20261011 rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩)
      (boundaryLaw.map realization) parameter point)
    (radius * natural.growth) natural.growth exponent clockAboveOne growthPositive interval.1 interval.2 exponentIdentity
    (actualSpectralData_diagonal_measurable_completion20261011 _ _ _ _ _ _ _ _ _ _ _ data point)
    (fun time _ => actualSpectralData_diagonal_nonnegative_completion20261011 _ _ _ _ _ _ _ _ _ _ _ data point time)
    (actualSpectralData_diagonal_antitone_completion20261011 _ _ _ _ _ _ _ _ _ _ _ data point)
    (actualSpectralData_diagonal_integrable_completion20261011 _ _ _ _ _ _ _ _ _ _ _ data point)
    (actualSpectralData_laplace_variational_completion20261011 _ _ _ _ _ _ _ _ _ _ _ data point)
    (actualSpectralData_resolvent_antitone_completion20261011 _ _ _ _ _ _ _ _ _ _ _ data point)
    (rational_clock_bounds_real_slack_completion20261011 diagonal natural.growth growthPositive point bounds)
  have exponentResult : 2 * exponent =
      2 * Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) /
        Real.log (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth) := by
    dsimp only [exponent, radius]
    ring
  rw [exponentResult] at result
  exact result

end
end IGSIII34.Spectral
