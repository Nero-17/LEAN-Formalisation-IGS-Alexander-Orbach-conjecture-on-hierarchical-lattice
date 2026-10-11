import IGSIII34.Spectral.ReciprocalCutoffSlackCompletion20261011
import IGSIII34.Spectral.ActualVariationalBoundsCompletion20261011
import IGSIII34.Spectral.HarmonicCompletionMeasurableCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms Resistance
open MeasureTheory Filter Matrix
open scoped BigOperators _root_.Topology

/-- The true diagonal resolvent has its lower Perron-clock exponent at
typical points. All localization, mass and energy bounds are derived from
the actual innovation field and original vertex-ratio weights. -/
theorem actual_diagonal_resolvent_clock_lower_completion20261011
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
      ∀ (anchor : ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) ⟨marks, typical⟩)),
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
          atTop (𝓝 (realization path))),
      (boundaryLaw.map realization).IsOpenPosMeasure →
      ∀ᵐ path ∂boundaryLaw, ∀ tolerance : ℝ, 1 < tolerance → ∀ᶠ depth in atTop,
        1 / (natural.growth^depth * tolerance^depth) ≤
        actualDiagonalVariationalResolventCompletion20261011 rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩)
          (boundaryLaw.map realization)
          ((((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth)^depth)
          (realization path) := by
  classical
  have radiusGreater : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  obtain ⟨_, edge, _⟩ := rule.network.exists_pivotal_configuration (classicalRule.connected _)
  have edgesPositive : 0 < (rule.edges : ℝ) := by
    exact_mod_cast lt_of_le_of_lt (Nat.zero_le edge.val) edge.isLt
  filter_upwards [actual_cutoff_clock_sequence_completion20261011 rule classicalRule p positive belowOne fixedPoint
    natural continuation weight actualRatios nonnegative] with marks sequence
  intro typical compactness anchor boundaryLaw probability atoms retainedPaths realization realizationMeasurable convergence fullSupport
  letI := compactness
  letI := probability
  letI : MeasurableSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) ⟨marks, typical⟩))) := borel _
  letI : BorelSpace (UniformSpace.Completion
    (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) ⟨marks, typical⟩))) := ⟨rfl⟩
  letI : IsProbabilityMeasure (boundaryLaw.map realization) := Measure.isProbabilityMeasure_map realizationMeasurable.aemeasurable
  letI := fullSupport
  have rational (slack : ℚ) : ∀ᵐ path ∂boundaryLaw, 1 < (slack : ℝ) → ∃ coefficient : ℝ,
      0 < coefficient ∧ ∀ divisor : ℕ, 0 < divisor → ∀ᶠ depth in atTop,
      ∃ potential : actualEnergyDomain rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩),
        1 / (natural.growth^depth * (slack : ℝ)^depth *
          (((rule.edges : ℝ) * natural.growth * (slack : ℝ))^(depth / divisor) + coefficient)) ≤
          actualDiagonalVariationalResolventCompletion20261011 rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
              (natural.amplitude • natural.field) ⟨marks, typical⟩)
            (boundaryLaw.map realization)
            ((((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth)^depth)
            (realization path) := by
    by_cases greater : 1 < (slack : ℝ)
    · obtain ⟨coefficient, coefficientPositive, cutoffs⟩ := sequence (slack : ℝ) greater
      filter_upwards [cutoffs typical compactness boundaryLaw probability atoms retainedPaths realization realizationMeasurable convergence fullSupport]
        with path estimates
      intro _
      refine ⟨coefficient, coefficientPositive, ?_⟩
      intro divisor divisorPositive
      filter_upwards [estimates divisor divisorPositive] with depth cutoff
      obtain ⟨potential, _, quotient⟩ := cutoff
      refine ⟨potential, quotient.trans ?_⟩
      exact actual_completion_quotient_le_diagonal_completion20261011 rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩)
        (boundaryLaw.map realization) anchor
        ((((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth)^depth)
        (one_le_pow₀ (one_le_mul_of_one_le_of_one_le radiusGreater.le natural.aboveOne.le)) (realization path) potential
    · exact Eventually.of_forall (fun _ impossible => (greater impossible).elim)
  filter_upwards [ae_all_iff.mpr rational] with path estimates
  intro tolerance greater
  obtain ⟨slack, slackGreater, divisor, divisorPositive, absorbs⟩ :=
    exists_rational_reciprocal_cutoff_slack_completion20261011 ((rule.edges : ℝ) * natural.growth)
      (mul_pos edgesPositive (zero_lt_one.trans natural.aboveOne)) tolerance greater
  obtain ⟨coefficient, coefficientPositive, clock⟩ := estimates slack slackGreater
  filter_upwards [clock divisor divisorPositive, absorbs coefficient coefficientPositive] with depth cutoff absorption
  obtain ⟨_, bound⟩ := cutoff
  have denominatorPositive : 0 < natural.growth^depth * (slack : ℝ)^depth *
      (((rule.edges : ℝ) * natural.growth * (slack : ℝ))^(depth / divisor) + coefficient) :=
    mul_pos (mul_pos (pow_pos (zero_lt_one.trans natural.aboveOne) depth)
      (pow_pos (zero_lt_one.trans slackGreater) depth))
      (add_pos_of_nonneg_of_pos (pow_pos (mul_pos (mul_pos edgesPositive
        (zero_lt_one.trans natural.aboveOne)) (zero_lt_one.trans slackGreater)) _).le coefficientPositive)
  apply (one_div_le_one_div_of_le denominatorPositive ?_).trans bound
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left absorption (pow_pos (zero_lt_one.trans natural.aboveOne) depth).le

end
end IGSIII34.Spectral
