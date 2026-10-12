import IGSIII34.Spectral.ActualCutoffQuotientCompletion
import IGSIII34.Spectral.BoundarySkeletonCompletion
import IGSIII34.Spectral.HarmonicCompletionMeasurableCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3600000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms Resistance
open MeasureTheory Filter Matrix
open scoped BigOperators _root_.Topology ENNReal

theorem singleton_measure_zero_of_localized_unit_functions
    {Point : Type*} [MeasurableSpace Point] (measure : Measure Point)
    (point : Point) (bound : ℕ → ℝ) (decay : Tendsto bound atTop (𝓝 0))
    (functions : ∀ᶠ depth in atTop, ∃ function : Point → ℝ,
      Integrable (fun other => function other ^ 2) measure ∧ function point = 1 ∧
      (∫ other, function other ^ 2 ∂measure) ≤ bound depth) :
    measure {point} = 0 := by
  have estimates : ∀ᶠ depth in atTop, measure {point} ≤ ENNReal.ofReal (bound depth) := by
    filter_upwards [functions] with depth function
    obtain ⟨function, integrable, atPoint, estimate⟩ := function
    apply (integrable.measure_le_integral (Eventually.of_forall (fun other => sq_nonneg _)) ?_).trans
      (ENNReal.ofReal_le_ofReal estimate)
    intro other member
    rcases Set.mem_singleton_iff.mp member with rfl
    simp only [atPoint, one_pow, le_refl]
  have upperLimit : Tendsto (fun depth => ENNReal.ofReal (bound depth)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp decay
  exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds upperLimit estimates) bot_le

theorem nullSingletonClass_map_of_ae_singleton_zero
    {Path Point : Type*} [MeasurableSpace Path] [MeasurableSpace Point]
    [MeasurableSingletonClass Point] (boundary : Measure Path)
    (realization : Path → Point) (measurable : Measurable realization)
    (zero : ∀ᵐ path ∂boundary, (boundary.map realization) {realization path} = 0) :
    NullSingletonClass (boundary.map realization) := by
  constructor
  intro point
  by_contra nonzero
  have preimageZero : boundary (realization ⁻¹' {point}) = 0 := by
    apply measure_mono_null _ (ae_iff.mp zero)
    intro path member
    have same : realization path = point := Set.mem_singleton_iff.mp member
    change ¬ (boundary.map realization) {realization path} = 0
    simpa only [same] using nonzero
  exact nonzero (by rw [Measure.map_apply measurable (measurableSet_singleton _)]; exact preimageZero)

/-- The actual mass measure has zero mass at every point. The proof uses
physical finite-energy cutoffs with shrinking square integral, produced
by actual collar avoidance and positive mass moments. In particular every
countable retained vertex skeleton is null, without identifying individual
realization fibres or assuming an inverse mass moment. -/
theorem actual_physical_mass_null_singletons
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
    (continuation : ActualMassContinuationCompletion rule p positive belowOne fixedPoint)
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
      ∀ (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
        (probability : IsProbabilityMeasure boundary)
        (atoms : ∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks))
        (retainedPaths : ∀ᵐ path ∂boundary, ∀ depth,
          Fin.init (path (depth + 1)) = path depth ∧ retainedComponentState rule marks (List.ofFn (path depth)) ≠ .inactive),
      ∀ (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
        ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩)
        (realizationMeasurable : Measurable realization)
        (convergence : ∀ᵐ path ∂boundary, Tendsto (fun depth =>
          actualElectricalComponentWordPoint rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) marks typical.1.1 depth (path (depth + 1)))
          atTop (𝓝 (realization path))),
      NullSingletonClass (boundary.map realization) := by
  classical
  have radiusAboveOne : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  obtain ⟨slack, slackAboveOne, slackBelowRadius⟩ := exists_between radiusAboveOne
  have radiusPositive := zero_lt_one.trans radiusAboveOne
  have ratioNonnegative : 0 ≤ slack /
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    div_nonneg (zero_lt_one.trans slackAboveOne).le radiusPositive.le
  have ratioBelowOne : slack /
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal < 1 :=
    (div_lt_one radiusPositive).mpr slackBelowRadius
  filter_upwards [actual_localized_cutoff_noncollar_paths_completion rule classicalRule p positive belowOne fixedPoint natural,
    actual_physical_socket_mass_subexponential_completion rule classicalRule p positive belowOne fixedPoint
      continuation weight actualRatios nonnegative,
    actual_boundary_all_reciprocal_collars_avoided_completion rule classicalRule p positive belowOne fixedPoint
      continuation weight actualRatios nonnegative]
    with marks cutoffs masses collars
  intro typical compactness boundary probability atoms retainedPaths realization realizationMeasurable convergence
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
  letI : IsProbabilityMeasure (boundary.map realization) :=
    Measure.isProbabilityMeasure_map realizationMeasurable.aemeasurable
  obtain ⟨cutoffThreshold, cutoffs⟩ := cutoffs slack slackAboveOne
  obtain ⟨coefficient, coefficientPositive, massThreshold, masses⟩ := masses slack slackAboveOne
  apply nullSingletonClass_map_of_ae_singleton_zero boundary realization realizationMeasurable
  filter_upwards [cutoffs typical compactness boundary probability retainedPaths realization realizationMeasurable convergence,
    collars boundary probability atoms] with path cutoffs avoids
  have eventuallyAvoids := (tendsto_add_atTop_nat 1).eventually (avoids 1 (by decide))
  simp only [Nat.div_one] at eventuallyAvoids
  have functions : ∀ᶠ depth in atTop,
      ∃ function : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ → ℝ,
      Integrable (fun other => function other ^ 2) (boundary.map realization) ∧
      function (realization path) = 1 ∧
      (∫ other, function other ^ 2 ∂boundary.map realization) ≤
        coefficient * (slack /
          (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (depth + 1) := by
    filter_upwards [eventuallyAvoids, eventually_ge_atTop cutoffThreshold,
      eventually_ge_atTop massThreshold] with depth avoids afterCutoff afterMass
    obtain ⟨potential, atPoint, _, _, integralBound⟩ := cutoffs depth depth (by omega) avoids
    refine ⟨actualEnergyExtensionLinear rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) ⟨marks, typical⟩) potential, ?_, atPoint, ?_⟩
    · exact actual_completion_square_integrable_completion rule p positive belowOne fixedPoint
        natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne)
        (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) ⟨marks, typical⟩) (boundary.map realization) potential
    · apply integralBound.trans
      have estimate := (le_div_iff₀ (pow_pos radiusPositive (depth + 1))).mpr
        (masses (depth + 1) (by omega) (fun index => (path (depth + 1) index).1) boundary atoms)
      simpa only [div_pow, mul_div_assoc] using estimate
  apply singleton_measure_zero_of_localized_unit_functions (boundary.map realization) (realization path) _ _ functions
  have decay := (tendsto_pow_atTop_nhds_zero_of_lt_one ratioNonnegative ratioBelowOne).comp
    (tendsto_add_atTop_nat 1)
  simpa only [mul_zero, Function.comp_def] using decay.const_mul coefficient

end
end IGSIII34.Spectral
