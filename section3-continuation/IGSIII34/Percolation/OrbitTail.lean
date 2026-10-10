import IGSIII34.Percolation.NormalizedOrbit
import IGSIII34.Percolation.EigenlawTail
import IGSIII.Chemical.SmallBall.UniformMoments

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork IGSIII34.Probability
open scoped NNReal ENNReal

theorem normalizedElectricalLaw_smallBall (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0)
    (meanPositive : 0 < electricalOutputMean rule parameter positive belowOne fixedPoint law)
    (threshold : ℝ) (thresholdNonnegative : 0 ≤ threshold) :
    (normalizedElectricalLaw rule parameter positive belowOne fixedPoint law : Measure ℝ≥0)
      {value | (value : ℝ) ≤ threshold} ≤
      ENNReal.ofReal (thinningMap rule.network parameter ((law : Measure ℝ≥0).real
        {value | (value : ℝ) ≤ ((rule.edges : ℝ) *
          electricalOutputMean rule parameter positive belowOne fixedPoint law) * threshold})) := by
  unfold normalizedElectricalLaw
  rw [scaledProbabilityLaw_measure, Measure.map_apply
    (f := fun value : ℝ≥0 => Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law)⁻¹ * value)
    (measurable_const.mul measurable_id)
    (measurableSet_le NNReal.continuous_coe.measurable measurable_const)]
  have eventEquality :
      (fun value : ℝ≥0 => Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law)⁻¹ * value) ⁻¹'
        {value | (value : ℝ) ≤ threshold} =
        {value : ℝ≥0 | (value : ℝ) ≤ electricalOutputMean rule parameter positive belowOne fixedPoint law * threshold} := by
    ext value
    change ((Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint law)⁻¹ * value : ℝ≥0) : ℝ) ≤ threshold ↔ _
    rw [NNReal.coe_mul, Real.coe_toNNReal _ (inv_nonneg.mpr meanPositive.le), inv_mul_le_iff₀ meanPositive]
    rfl
  rw [eventEquality]
  convert electricalOutputLaw_smallBall_le rule parameter positive belowOne fixedPoint law
    (electricalOutputMean rule parameter positive belowOne fixedPoint law * threshold)
    (mul_nonneg meanPositive.le thresholdNonnegative) using 1
  simp only [thinningMap, Measure.real_def, mul_assoc]

theorem normalizedElectricalOrbit_smallBall_step (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ)
    (threshold : ℝ) (thresholdNonnegative : 0 ≤ threshold) :
    (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint (depth + 1) : Measure ℝ≥0).real
      {value | (value : ℝ) ≤ threshold} ≤
      thinningMap rule.network parameter
        ((normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0).real
          {value | (value : ℝ) ≤ ((rule.edges : ℝ)^2 + 1) * threshold}) := by
  have instability := rule.network.interior_fixed_point_strictly_unstable
    parameter positive belowOne fixedPoint classical.scale
  have bounds := normalizedElectricalOrbit_outputMean_bounds rule classical parameter positive belowOne fixedPoint depth
  have meanPositive := (zero_lt_one.trans instability).trans_le bounds.1
  have estimate := normalizedElectricalLaw_smallBall rule parameter positive belowOne fixedPoint
    (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth) meanPositive threshold thresholdNonnegative
  rw [← normalizedElectricalOrbit_succ] at estimate
  have realEstimate := ENNReal.toReal_mono ENNReal.ofReal_ne_top estimate
  rw [ENNReal.toReal_ofReal (thinningMap_nonnegative rule.network positive belowOne measureReal_nonneg measureReal_le_one)]
    at realEstimate
  apply realEstimate.trans
  apply thinningMap_monotoneOn rule.network positive belowOne
    ⟨measureReal_nonneg, measureReal_le_one⟩ ⟨measureReal_nonneg, measureReal_le_one⟩
  apply measureReal_mono
  intro value small
  change (value : ℝ) ≤ _ at small ⊢
  apply small.trans
  apply mul_le_mul_of_nonneg_right _ thresholdNonnegative
  nlinarith [mul_le_mul_of_nonneg_left bounds.2 (Nat.cast_nonneg rule.edges : (0 : ℝ) ≤ rule.edges)]
  all_goals exact measure_ne_top _ _

theorem normalizedElectricalOrbit_uniform_smallBall_start (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ∃ start : ℝ, 0 ≤ start ∧ start < 1 ∧ ∀ depth,
      (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0).real
        {value | (value : ℝ) ≤ (1 / 2 : ℝ)} ≤ start := by
  obtain ⟨bound, momentBound⟩ := normalizedElectricalOrbit_uniform_moment rule classical parameter positive belowOne fixedPoint 2
  let constant : ℝ := 1 + bound
  have constantAtLeastOne : 1 ≤ constant := le_add_of_nonneg_right bound.property
  have constantPositive : 0 < constant := zero_lt_one.trans_le constantAtLeastOne
  refine ⟨1 - 1 / (4 * constant), ?_, ?_, ?_⟩
  · apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : 0 < 4 * constant)).mpr
    linarith
  · exact sub_lt_self _ (by positivity)
  · intro depth
    have squareIntegrable : Integrable (fun value : ℝ≥0 => (value : ℝ)^2)
        (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0) := by
      have result := integrable_toReal_of_lintegral_ne_top
        (measurable_id.coe_nnreal_ennreal.pow_const 2).aemeasurable
        (ne_top_of_le_ne_top ENNReal.coe_ne_top (momentBound depth))
      simpa only [ENNReal.toReal_pow, ENNReal.coe_toReal, id_eq] using result
    apply IGSIII.Chemical.SmallBall.smallBall_half_le_of_mean_one_second_moment_bound _
      NNReal.continuous_coe.measurable
      (integrable_coe_of_secondMoment_bound _ bound (momentBound depth)) squareIntegrable
      (normalizedElectricalOrbit_mean_one rule classical parameter positive belowOne fixedPoint depth) constantPositive
    have integralBound := integral_coe_le_of_lintegral_coe_le
      (f := fun value : ℝ≥0 => value^2) (b := bound)
      (by simpa only [ENNReal.coe_pow] using momentBound depth)
    have converted : (∫ value : ℝ≥0, (value : ℝ)^2
        ∂(normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0)) ≤ bound := by
      simpa only [NNReal.coe_pow] using integralBound
    exact converted.trans (by dsimp [constant]; linarith)

theorem uniform_seeded_tail_le_iterate_on {map : ℝ → ℝ} {domain : Set ℝ}
    {tail : ℕ → ℕ → ℝ} {start : ℝ}
    (monotone : MonotoneOn map domain)
    (orbitWithin : ∀ scale, map^[scale] start ∈ domain)
    (orbitNonnegative : ∀ scale, 0 ≤ map^[scale] start)
    (tailWithin : ∀ depth scale, tail depth scale ∈ domain)
    (initial : ∀ depth, tail depth 0 ≤ start)
    (seed : ∀ scale, tail 0 (scale + 1) = 0)
    (step : ∀ depth scale, tail (depth + 1) (scale + 1) ≤ map (tail depth scale)) :
    ∀ depth scale, tail depth scale ≤ map^[scale] start := by
  intro depth scale
  induction scale generalizing depth with
  | zero => exact initial depth
  | succ scale previous =>
    cases depth with
    | zero => rw [seed]; exact orbitNonnegative _
    | succ depth =>
      rw [Function.iterate_succ_apply']
      exact (step depth scale).trans
        (monotone (tailWithin depth scale) (orbitWithin scale) (previous depth))

theorem normalizedElectricalOrbit_uniform_thinning_tail (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ∃ start : ℝ, 0 ≤ start ∧ start < 1 ∧ ∀ depth scale,
      (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0).real
        {value | (value : ℝ) ≤ (1 / 2 : ℝ) / ((rule.edges : ℝ)^2 + 1)^scale} ≤
        (thinningMap rule.network parameter)^[scale] start := by
  obtain ⟨start, startNonnegative, startBelowOne, initial⟩ :=
    normalizedElectricalOrbit_uniform_smallBall_start rule classical parameter positive belowOne fixedPoint
  have baseAboveOne : 1 < (rule.edges : ℝ)^2 + 1 := by
    obtain ⟨_, edge, _⟩ := rule.network.exists_pivotal_configuration (classical.connected _)
    have edgesPositive : (0 : ℝ) < rule.edges := by exact_mod_cast Nat.zero_lt_of_lt edge.isLt
    nlinarith
  have basePositive := zero_lt_one.trans baseAboveOne
  have orbitBounds := iterate_bounds startNonnegative startBelowOne
    (thinningMap_zero rule.network parameter)
    (fun value nonnegative below => thinningMap_nonnegative rule.network positive belowOne nonnegative below.le)
    (fun value positiveValue below => thinningMap_strict rule.network positive belowOne fixedPoint classical.scale positiveValue below)
  refine ⟨start, startNonnegative, startBelowOne, ?_⟩
  apply uniform_seeded_tail_le_iterate_on
    (domain := Set.Icc 0 1)
    (tail := fun depth scale =>
      (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0).real
        {value | (value : ℝ) ≤ (1 / 2 : ℝ) / ((rule.edges : ℝ)^2 + 1)^scale})
    (thinningMap_monotoneOn rule.network positive belowOne)
    (fun scale => ⟨(orbitBounds scale).1, (orbitBounds scale).2.trans startBelowOne.le⟩)
    (fun scale => (orbitBounds scale).1)
    (fun _ _ => ⟨measureReal_nonneg, measureReal_le_one⟩)
  · simpa only [pow_zero, div_one] using initial
  · intro scale
    have powerPositive := pow_pos basePositive (scale + 1)
    have powerAtLeastOne : 1 ≤ ((rule.edges : ℝ)^2 + 1)^(scale + 1) := one_le_pow₀ baseAboveOne.le
    have halfBound : (1 / 2 : ℝ) / ((rule.edges : ℝ)^2 + 1)^(scale+1) ≤ 1 / 2 := by
      apply (div_le_iff₀ powerPositive).mpr
      nlinarith
    have notSmall : ¬ (1 : ℝ) ≤ (1 / 2 : ℝ) / ((rule.edges : ℝ)^2 + 1)^(scale+1) := by linarith
    rw [normalizedElectricalOrbit_zero]
    change (Measure.dirac (1 : ℝ≥0)).real
      {value : ℝ≥0 | (value : ℝ) ≤ (1 / 2 : ℝ) / ((rule.edges : ℝ)^2 + 1)^(scale+1)} = 0
    have notMember : (1 : ℝ≥0) ∉
        {value : ℝ≥0 | (value : ℝ) ≤ (1 / 2 : ℝ) / ((rule.edges : ℝ)^2 + 1)^(scale+1)} := notSmall
    rw [Measure.real_def, Measure.dirac_apply, Set.indicator_of_notMem notMember]
    rfl
  · intro depth scale
    have estimate := normalizedElectricalOrbit_smallBall_step rule classical parameter positive belowOne fixedPoint depth
      ((1 / 2 : ℝ) / ((rule.edges : ℝ)^2+1)^(scale+1))
      (div_nonneg (by norm_num) (pow_pos basePositive _).le)
    have thresholdEquality : ((rule.edges : ℝ)^2+1) *
        ((1 / 2 : ℝ) / ((rule.edges : ℝ)^2+1)^(scale+1)) =
        (1 / 2 : ℝ) / ((rule.edges : ℝ)^2+1)^scale := by
      rw [pow_succ]
      field_simp
      simp [pow_succ, mul_comm]
    simpa only [thresholdEquality] using estimate

end
end IGSIII34.Percolation
