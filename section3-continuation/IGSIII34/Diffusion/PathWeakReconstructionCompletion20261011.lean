import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! Full path weak convergence from finite reconstructions and genuine
probability modulus bounds. The path topology can be nonseparable; all
bad sets are measurably established on the original sample spaces. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal BoundedContinuousFunction
variable {Path Outcome : Type*} [PseudoMetricSpace Path]
  [MeasurableSpace Path] [OpensMeasurableSpace Path] [MeasurableSpace Outcome]

theorem bounded_lipschitz_sample_integral_error_completion20261011
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (sample approximation : Outcome → Path)
    (sampleMeasurable : Measurable sample) (approximationMeasurable : Measurable approximation)
    (test : Path →ᵇ ℝ) (constant : ℝ≥0) (lipschitz : LipschitzWith constant test)
    (bad : Set Outcome) (badMeasurable : MeasurableSet bad)
    (duration : ℝ) (durationNonnegative : 0 ≤ duration)
    (close : ∀ outcome, outcome ∉ bad → dist (sample outcome) (approximation outcome) ≤ duration) :
    ‖(∫ outcome, test (sample outcome) ∂law) - ∫ outcome, test (approximation outcome) ∂law‖ ≤
      (constant : ℝ) * duration + 2 * ‖test‖ * law.real bad := by
  have firstIntegrable : Integrable (fun outcome => test (sample outcome)) law :=
    Integrable.of_bound (test.continuous.stronglyMeasurable.comp_measurable sampleMeasurable).aestronglyMeasurable
      ‖test‖ (Eventually.of_forall (fun outcome => BoundedContinuousFunction.norm_coe_le_norm test _))
  have secondIntegrable : Integrable (fun outcome => test (approximation outcome)) law :=
    Integrable.of_bound (test.continuous.stronglyMeasurable.comp_measurable approximationMeasurable).aestronglyMeasurable
      ‖test‖ (Eventually.of_forall (fun outcome => BoundedContinuousFunction.norm_coe_le_norm test _))
  let difference := fun outcome => test (sample outcome) - test (approximation outcome)
  have differenceIntegrable : Integrable difference law := firstIntegrable.sub secondIntegrable
  have badBound : ‖∫ outcome in bad, difference outcome ∂law‖ ≤ 2 * ‖test‖ * law.real bad := by
    apply norm_setIntegral_le_of_norm_le_const_ae' (measure_lt_top _ _)
    apply Eventually.of_forall
    intro outcome _
    exact (norm_sub_le _ _).trans (by nlinarith [BoundedContinuousFunction.norm_coe_le_norm test (sample outcome),
      BoundedContinuousFunction.norm_coe_le_norm test (approximation outcome)])
  have goodBound : ‖∫ outcome in badᶜ, difference outcome ∂law‖ ≤ (constant : ℝ) * duration * law.real badᶜ := by
    apply norm_setIntegral_le_of_norm_le_const_ae' (measure_lt_top _ _)
    apply Eventually.of_forall
    intro outcome member
    change ‖test (sample outcome) - test (approximation outcome)‖ ≤ _
    rw [← dist_eq_norm]
    exact (lipschitz.dist_le_mul _ _).trans
      (mul_le_mul_of_nonneg_left (close outcome member) constant.coe_nonneg)
  have complementMass : law.real badᶜ ≤ 1 := by
    simpa only [probReal_univ] using measureReal_mono (μ := law) (show badᶜ ⊆ univ from subset_univ _)
  rw [← integral_sub firstIntegrable secondIntegrable]
  change ‖∫ outcome, difference outcome ∂law‖ ≤ _
  rw [← integral_add_compl badMeasurable differenceIntegrable]
  exact (norm_add_le _ _).trans ((add_le_add badBound goodBound).trans (by
    have := mul_le_mul_of_nonneg_left complementMass (mul_nonneg constant.coe_nonneg durationNonnegative)
    linarith))

theorem probability_sample_weak_of_reconstructions_completion20261011
    {Samples : ℕ → Type*} [∀ index, MeasurableSpace (Samples index)]
    (laws : ∀ index, Measure (Samples index)) [∀ index, IsProbabilityMeasure (laws index)]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (samples : ∀ index, Samples index → Path) (sample : Outcome → Path)
    (samplesMeasurable : ∀ index, Measurable (samples index)) (sampleMeasurable : Measurable sample)
    (reconstructions : ℕ → ∀ index, Samples index → Path) (reconstruction : ℕ → Outcome → Path)
    (reconstructionsMeasurable : ∀ grid index, Measurable (reconstructions grid index))
    (reconstructionMeasurable : ∀ grid, Measurable (reconstruction grid))
    (weakReconstructions : ∀ grid,
      Tendsto (fun index => ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Samples index))
        (reconstructionsMeasurable grid index).aemeasurable) atTop
        (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome) (reconstructionMeasurable grid).aemeasurable)))
    (probabilityApproximation : ∀ duration error : ℝ, 0 < duration → 0 < error →
      ∃ grid : ℕ,
        (∀ᶠ index in atTop, ∃ bad : Set (Samples index), MeasurableSet bad ∧ (laws index).real bad ≤ error ∧
          ∀ outcome, outcome ∉ bad → dist (samples index outcome) (reconstructions grid index outcome) ≤ duration) ∧
        (∃ bad : Set Outcome, MeasurableSet bad ∧ law.real bad ≤ error ∧
          ∀ outcome, outcome ∉ bad → dist (sample outcome) (reconstruction grid outcome) ≤ duration)) :
    Tendsto (fun index => ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Samples index))
      (samplesMeasurable index).aemeasurable) atTop
      (𝓝 (ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome) sampleMeasurable.aemeasurable)) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro function bounded lipschitz
  obtain ⟨constant, lipschitz⟩ := lipschitz
  let test : Path →ᵇ ℝ := { toFun := function, continuous_toFun := lipschitz.continuous, map_bounded' := bounded }
  have mappedIntegral (index : ℕ) :
      (∫ path, function path ∂(ProbabilityMeasure.map (⟨laws index, inferInstance⟩ : ProbabilityMeasure (Samples index))
        (samplesMeasurable index).aemeasurable : Measure Path)) = ∫ outcome, test (samples index outcome) ∂laws index := by
    exact integral_map (μ := laws index) (samplesMeasurable index).aemeasurable test.continuous.aestronglyMeasurable
  have limitIntegral :
      (∫ path, function path ∂(ProbabilityMeasure.map (⟨law, inferInstance⟩ : ProbabilityMeasure Outcome)
        sampleMeasurable.aemeasurable : Measure Path)) = ∫ outcome, test (sample outcome) ∂law := by
    exact integral_map (μ := law) sampleMeasurable.aemeasurable test.continuous.aestronglyMeasurable
  simp only [mappedIntegral, limitIntegral]
  apply Metric.tendsto_nhds.mpr
  intro epsilon epsilonPositive
  let duration := epsilon / (6 * ((constant : ℝ) + 1))
  let error := epsilon / (12 * (‖test‖ + 1))
  have durationPositive : 0 < duration := by dsimp [duration]; positivity
  have errorPositive : 0 < error := by dsimp [error]; positivity
  have durationIdentity : 6 * ((constant : ℝ) + 1) * duration = epsilon := by
    dsimp [duration]
    field_simp
  have errorIdentity : 12 * (‖test‖ + 1) * error = epsilon := by
    dsimp [error]
    field_simp
  have nearBound : (constant : ℝ) * duration + 2 * ‖test‖ * error < epsilon / 3 := by
    nlinarith [constant.coe_nonneg, norm_nonneg test]
  obtain ⟨grid, finiteApproximation, bad, badMeasurable, badProbability, limitClose⟩ :=
    probabilityApproximation duration error durationPositive errorPositive
  have limitError := (bounded_lipschitz_sample_integral_error_completion20261011 law sample (reconstruction grid)
    sampleMeasurable (reconstructionMeasurable grid) test constant lipschitz bad badMeasurable duration durationPositive.le limitClose).trans
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left badProbability (show 0 ≤ 2 * ‖test‖ by positivity)))
  have reconstructedConvergence : Tendsto (fun index => ∫ outcome, test (reconstructions grid index outcome) ∂laws index)
      atTop (𝓝 (∫ outcome, test (reconstruction grid outcome) ∂law)) := by
    have weak := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp (weakReconstructions grid)) test
    simpa only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.coe_mk, integral_map (reconstructionsMeasurable grid _).aemeasurable test.continuous.aestronglyMeasurable,
      integral_map (reconstructionMeasurable grid).aemeasurable test.continuous.aestronglyMeasurable] using weak
  filter_upwards [finiteApproximation, reconstructedConvergence.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < epsilon / 3))]
    with index finiteApproximation reconstructedClose
  obtain ⟨finiteBad, finiteBadMeasurable, finiteBadProbability, finiteClose⟩ := finiteApproximation
  have finiteError := (bounded_lipschitz_sample_integral_error_completion20261011 (laws index) (samples index) (reconstructions grid index)
    (samplesMeasurable index) (reconstructionsMeasurable grid index) test constant lipschitz finiteBad finiteBadMeasurable duration durationPositive.le finiteClose).trans
      (add_le_add (le_refl _) (mul_le_mul_of_nonneg_left finiteBadProbability (show 0 ≤ 2 * ‖test‖ by positivity)))
  have triangle := (dist_triangle
    (∫ outcome, test (samples index outcome) ∂laws index) (∫ outcome, test (reconstructions grid index outcome) ∂laws index)
    (∫ outcome, test (sample outcome) ∂law)).trans
    (add_le_add le_rfl (dist_triangle (∫ outcome, test (reconstructions grid index outcome) ∂laws index)
      (∫ outcome, test (reconstruction grid outcome) ∂law) (∫ outcome, test (sample outcome) ∂law)))
  rw [← dist_eq_norm] at finiteError
  rw [← dist_eq_norm, dist_comm] at limitError
  change dist (∫ outcome, test (reconstructions grid index outcome) ∂laws index)
    (∫ outcome, test (reconstruction grid outcome) ∂law) < epsilon / 3 at reconstructedClose
  linarith

end
end IGSIII34.Diffusion







