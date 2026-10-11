import IGSIII34.Spectral.ActualCutoffQuotientCompletion20261011
import IGSIII34.Spectral.BoundarySkeletonCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms Resistance
open MeasureTheory Filter Matrix
open scoped BigOperators _root_.Topology

theorem cutoff_clock_denominator_identity_completion20261011
    (edges resistance slack radius coefficient : ℝ) (radiusPositive : 0 < radius)
    (depth refinement : ℕ) :
    edges^refinement * resistance^(depth + refinement) * slack^(depth + refinement) +
      (radius * resistance)^depth * (coefficient * slack^depth / radius^depth) =
    resistance^depth * slack^depth * ((edges * resistance * slack)^refinement + coefficient) := by
  rw [pow_add, pow_add, mul_pow, mul_pow, mul_pow]
  field_simp [(pow_pos radiusPositive depth).ne']
  <;> ring

/-- Every reciprocal-integer refinement schedule gives actual cutoffs
at typical boundary points. The denominator is normalized by the actual
Perron-resistance clock, retaining the exact geometric slack. -/
theorem actual_cutoff_clock_sequence_completion20261011
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
      ∀ slack : ℝ, 1 < slack → ∃ coefficient : ℝ, 0 < coefficient ∧
      ∀ (typical : StationaryHarmonicTypical rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) marks),
      ∀ (compactness : CompactSpace (UniformSpace.Completion
        (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩)))),
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
      ∀ᵐ path ∂boundaryLaw, ∀ divisor : ℕ, 0 < divisor → ∀ᶠ depth in atTop,
        ∃ potential : actualEnergyDomain rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩),
          actualEnergyExtensionLinear rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
              (natural.amplitude • natural.field) ⟨marks, typical⟩) potential (realization path) = 1 ∧
          1 / (natural.growth^depth * slack^depth *
            (((rule.edges : ℝ) * natural.growth * slack)^(depth / divisor) + coefficient)) ≤
          actualEnergyExtensionLinear rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
            (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
              (natural.amplitude • natural.field) ⟨marks, typical⟩) potential (realization path)^2 /
            (limitingEnergy
              (actualEnergyEndpoint rule p positive belowOne fixedPoint natural.growth
                (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
                (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
                  (natural.amplitude • natural.field) ⟨marks, typical⟩))
              (actualEnergyConductance rule p positive belowOne fixedPoint natural.growth
                (natural.amplitude • natural.field)
                (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
                  (natural.amplitude • natural.field) ⟨marks, typical⟩)) potential.val +
              (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth)^depth *
              ∫ point, actualEnergyExtensionLinear rule p positive belowOne fixedPoint natural.growth
                (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
                (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
                  (natural.amplitude • natural.field) ⟨marks, typical⟩) potential point^2 ∂(boundaryLaw.map realization)) := by
  classical
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  filter_upwards [actual_localized_cutoff_noncollar_paths_completion20261011 rule classicalRule p positive belowOne fixedPoint natural,
    actual_physical_socket_mass_subexponential_completion20261011 rule classicalRule p positive belowOne fixedPoint continuation weight actualRatios nonnegative,
    actual_boundary_all_reciprocal_collars_avoided_completion20261011 rule classicalRule p positive belowOne fixedPoint continuation weight actualRatios nonnegative]
    with marks cutoffs masses collars
  intro slack greater
  obtain ⟨threshold, cutoffs⟩ := cutoffs slack greater
  obtain ⟨coefficient, coefficientPositive, massThreshold, masses⟩ := masses slack greater
  refine ⟨coefficient, coefficientPositive, ?_⟩
  intro typical compactness boundaryLaw probability atoms retainedPaths realization realizationMeasurable convergence fullSupport
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
  filter_upwards [cutoffs typical compactness boundaryLaw probability retainedPaths realization realizationMeasurable convergence,
    collars boundaryLaw probability atoms] with path cutoffs avoids
  intro divisor divisorPositive
  filter_upwards [eventually_ge_atTop (max (max threshold massThreshold) (divisor + 1)), avoids divisor divisorPositive]
    with depth after avoids
  have depthPositive : 0 < depth := by omega
  have refinementPositive : 0 < depth / divisor := Nat.div_pos (by omega) divisorPositive
  obtain ⟨coarse, rfl⟩ := Nat.exists_eq_succ_of_ne_zero depthPositive.ne'
  obtain ⟨fine, fineEq⟩ := Nat.exists_eq_succ_of_ne_zero refinementPositive.ne'
  change (coarse + 1) / divisor = fine + 1 at fineEq
  have totalEq : coarse + fine + 2 = (coarse + 1) + (coarse + 1) / divisor := by omega
  have noncollar : path ∉ terminalCylinderCollarCompletion20261011 rule 0 (coarse + 1) (fine + 1) := by
    simpa only [fineEq] using avoids
  obtain ⟨potential, atPoint, _, energyEstimate, massEstimate⟩ := cutoffs coarse fine
    (by omega) noncollar
  have socketMass := masses (coarse + 1) (by omega) (fun index => (path (coarse + 1) index).1) boundaryLaw atoms
  have normEstimate := massEstimate.trans ((le_div_iff₀ (pow_pos radiusPositive (coarse + 1))).mpr socketMass)
  have quotient := actual_completion_cutoff_quotient_lower_completion20261011 rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩)
    (boundaryLaw.map realization) potential (realization path) atPoint _ _ energyEstimate normEstimate
    ((((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth)^(coarse + 1))
    (pow_pos (mul_pos radiusPositive (zero_lt_one.trans natural.aboveOne)) (coarse + 1))
  have refinementEq : fine + 1 = (coarse + 1) / divisor := by omega
  rw [refinementEq, totalEq,
    cutoff_clock_denominator_identity_completion20261011 _ _ _ _ _ radiusPositive] at quotient
  exact ⟨potential, atPoint, quotient⟩

end
end IGSIII34.Spectral
