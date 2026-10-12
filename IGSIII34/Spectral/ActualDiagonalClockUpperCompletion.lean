import IGSIII34.Spectral.NaturalMeshSlacksCompletion
import IGSIII34.Spectral.HarmonicCompletionMeasurableCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms Resistance
open MeasureTheory Filter Matrix
open scoped BigOperators _root_.Topology

/-- The typical upper diagonal exponent uses the actual physical radius
mesh and the same actual vertex-ratio cylinder mass. Averaging occurs on
the genuine boundary cylinder, so no image-cell measurability is assumed. -/
theorem actual_diagonal_resolvent_clock_upper_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
    (weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks))) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
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
      ∀ᵐ path ∂boundaryLaw, ∀ tolerance : ℝ, 1 < tolerance → ∀ᶠ depth in atTop,
        actualDiagonalVariationalResolventCompletion rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
          (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) ⟨marks, typical⟩)
          (boundaryLaw.map realization)
          ((((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth)^depth)
          (realization path) ≤ tolerance^depth / natural.growth^depth := by
  have growthPositive := zero_lt_one.trans natural.aboveOne
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  have meshEvents := ae_all_iff.mpr (fun index : ℕ => natural_physical_boundary_anchor_mesh_completion
    rule classicalRule p positive belowOne fixedPoint natural
    (resistanceMeshSlackCompletion natural.growth index / natural.growth)
    (div_pos (zero_lt_one.trans (resistance_mesh_slack_bounds_completion natural.growth natural.aboveOne index).1) growthPositive)
    ((div_lt_one growthPositive).mpr (resistance_mesh_slack_bounds_completion natural.growth natural.aboveOne index).2)
    (by simpa only [mul_div_cancel₀ _ growthPositive.ne'] using
      (resistance_mesh_slack_bounds_completion natural.growth natural.aboveOne index).1))
  filter_upwards [meshEvents, actual_boundary_vertex_ratio_typical_lower_completion
    rule classicalRule p positive belowOne fixedPoint weight actualRatios] with marks meshes masses
  intro typical compactness boundaryLaw probability atoms retainedPaths realization realizationMeasurable convergence
  letI := compactness
  letI := probability
  choose thresholds meshes using meshes
  have pairs (index : ℕ) := boundary_same_prefix_distance_completion boundaryLaw
    (fun depth word => actualElectricalComponentWordPoint rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) growthPositive marks typical.1.1 depth word) realization (thresholds index)
    ((rule.edges + 1 : ℝ) / (1 - resistanceMeshSlackCompletion natural.growth index / natural.growth)^2)
    (resistanceMeshSlackCompletion natural.growth index / natural.growth)
    (meshes index typical.1.1 boundaryLaw retainedPaths realization convergence)
  filter_upwards [ae_all_iff.mpr pairs, masses boundaryLaw atoms] with path pairs masses
  intro tolerance toleranceGreater
  obtain ⟨index, slackBelow⟩ := resistance_mesh_slack_eventually_small_completion natural.growth natural.aboveOne tolerance toleranceGreater
  let slack := resistanceMeshSlackCompletion natural.growth index
  let eta := slack / natural.growth
  let coefficient := (rule.edges + 1 : ℝ) / (1 - eta)^2
  have slackGreater : 1 < slack := (resistance_mesh_slack_bounds_completion natural.growth natural.aboveOne index).1
  have slackPositive := zero_lt_one.trans slackGreater
  have etaPositive : 0 < eta := div_pos slackPositive growthPositive
  have etaBelowOne : eta < 1 := (div_lt_one growthPositive).mpr
    (resistance_mesh_slack_bounds_completion natural.growth natural.aboveOne index).2
  have coefficientPositive : 0 < coefficient := div_pos (by positivity) (sq_pos_of_pos (sub_pos.mpr etaBelowOne))
  let totalCoefficient := 2 * max 1 (2 * coefficient)
  filter_upwards [eventually_ge_atTop (thresholds index + 1), masses.2 slack slackGreater,
    clock_upper_constant_absorption_completion natural.growth slack tolerance totalCoefficient growthPositive slackPositive slackBelow]
    with depth after massLower absorption
  have depthPositive : 0 < depth := by omega
  obtain ⟨coarse, rfl⟩ := Nat.exists_eq_succ_of_ne_zero depthPositive.ne'
  let cylinder : Set (Π depth, Fin depth → (Fin rule.edges × Bool)) := {other | other (coarse + 1) = path (coarse + 1)}
  have cylinderMeasurable : MeasurableSet cylinder := measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  have cylinderMass : boundaryLaw.real cylinder = weight (List.ofFn (path (coarse + 1))) marks := by
    rw [Measure.real_def, atoms, ENNReal.toReal_ofReal (masses.1 (coarse + 1)).le]
  have massPositive : 0 < boundaryLaw.real cylinder := by rw [cylinderMass]; exact masses.1 (coarse + 1)
  have inverseMass := inverse_clock_mass_bound_completion
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) natural.growth slack
    (weight (List.ofFn (path (coarse + 1))) marks) radiusPositive growthPositive slackPositive
    (masses.1 (coarse + 1)) (coarse + 1) massLower.le
  have diagonal := actual_boundary_diagonal_local_upper_completion rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth (natural.amplitude • natural.field) ⟨marks, typical⟩)
    boundaryLaw realization realizationMeasurable path cylinder cylinderMeasurable massPositive
    (2 * coefficient * eta^(coarse + 1)) (by positivity) (pairs index coarse (by omega))
    ((((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth)^(coarse + 1))
    (pow_pos (mul_pos radiusPositive growthPositive) (coarse + 1))
  rw [cylinderMass] at diagonal
  have first : 1 / ((((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * natural.growth)^(coarse + 1) *
      weight (List.ofFn (path (coarse + 1))) marks) ≤ max 1 (2 * coefficient) * eta^(coarse + 1) :=
    inverseMass.trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) (2 * coefficient)) (pow_pos etaPositive (coarse + 1)).le)
  have second : 2 * coefficient * eta^(coarse + 1) ≤ max 1 (2 * coefficient) * eta^(coarse + 1) :=
    mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) (2 * coefficient)) (pow_pos etaPositive (coarse + 1)).le
  have upper := diagonal.trans (mul_le_mul_of_nonneg_left (max_le first second) (by norm_num : 0 ≤ (2 : ℝ)))
  exact upper.trans (by simpa only [totalCoefficient, eta, mul_assoc] using absorption)

end
end IGSIII34.Spectral
