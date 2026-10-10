import IGSIII.Chemical.SmallBall.UniformMoments
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Uniform small-ball estimates imply uniform Laplace decay.  This is the
analytic ingredient for path-counting estimates and the mean growth comparison. -/

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open MeasureTheory Set Filter
open scoped Topology

noncomputable section

variable {Sample : Type*} [MeasurableSpace Sample]

theorem integrable_exp_neg_mul (measure : Measure Sample) [IsFiniteMeasure measure]
    {value : Sample → ℝ} (measurable : Measurable value)
    (nonnegative : ∀ sample, 0 ≤ value sample)
    {parameter : ℝ} (parameterNonnegative : 0 ≤ parameter) :
    Integrable (fun sample => Real.exp (-parameter * value sample)) measure := by
  apply (integrable_const (1 : ℝ)).mono'
    (Real.continuous_exp.measurable.comp (measurable_const.mul measurable)).aestronglyMeasurable
  filter_upwards with sample
  change ‖Real.exp (-parameter * value sample)‖ ≤ 1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr parameterNonnegative) (nonnegative sample))

theorem laplace_le_smallBall (measure : Measure Sample) [IsProbabilityMeasure measure]
    {value : Sample → ℝ} (measurable : Measurable value)
    (nonnegative : ∀ sample, 0 ≤ value sample)
    {parameter : ℝ} (parameterNonnegative : 0 ≤ parameter) (cutoff : ℝ) :
    (∫ sample, Real.exp (-parameter * value sample) ∂measure) ≤
      measure.real {sample | value sample ≤ cutoff} + Real.exp (-parameter * cutoff) := by
  have measurableEvent : MeasurableSet {sample | value sample ≤ cutoff} :=
    measurableSet_le measurable measurable_const
  have indicatorIntegrable : Integrable
      ({sample | value sample ≤ cutoff}.indicator (fun _ => (1 : ℝ))) measure :=
    (integrable_const (1 : ℝ)).indicator measurableEvent
  have upperIntegrable := indicatorIntegrable.add (integrable_const (Real.exp (-parameter * cutoff)))
  have comparison := integral_mono (integrable_exp_neg_mul measure measurable nonnegative
      parameterNonnegative) upperIntegrable (fun sample => by
    change Real.exp (-parameter * value sample) ≤
      {sample | value sample ≤ cutoff}.indicator (fun _ => (1 : ℝ)) sample +
        Real.exp (-parameter * cutoff)
    by_cases small : value sample ≤ cutoff
    · rw [Set.indicator_of_mem (show sample ∈ {sample | value sample ≤ cutoff} from small)]
      have bounded := Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr parameterNonnegative) (nonnegative sample))
      exact bounded.trans (le_add_of_nonneg_right (Real.exp_nonneg _))
    · rw [Set.indicator_of_notMem
        (show sample ∉ {sample | value sample ≤ cutoff} from small), zero_add]
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left (le_of_not_ge small) (neg_nonpos.mpr parameterNonnegative)))
  change (∫ sample, Real.exp (-parameter * value sample) ∂measure) ≤
    (∫ sample, {sample | value sample ≤ cutoff}.indicator (fun _ => (1 : ℝ)) sample +
      Real.exp (-parameter * cutoff) ∂measure) at comparison
  simpa only [integral_add indicatorIntegrable (integrable_const _),
    integral_indicator_const (1 : ℝ) measurableEvent, integral_const, probReal_univ,
    smul_eq_mul, one_mul, mul_one] using comparison

theorem exists_uniform_laplace_bound {Index : Type*}
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Index → Sample → ℝ) (measurable : ∀ index, Measurable (value index))
    (nonnegative : ∀ index sample, 0 ≤ value index sample)
    (smallBalls : ∀ error : ℝ, 0 < error → ∃ cutoff : ℝ, 0 < cutoff ∧
      ∀ index, measure.real {sample | value index sample ≤ cutoff} ≤ error)
    {target : ℝ} (targetPositive : 0 < target) :
    ∃ parameter : ℝ, 0 < parameter ∧ ∀ index,
      (∫ sample, Real.exp (-parameter * value index sample) ∂measure) ≤ target := by
  have errorPositive : 0 < min (target / 2) (1 / 2 : ℝ) :=
    lt_min (div_pos targetPositive (by norm_num)) (by norm_num)
  have errorBelowOne : min (target / 2) (1 / 2 : ℝ) < 1 :=
    (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨cutoff, cutoffPositive, smallBallBound⟩ :=
    smallBalls (min (target / 2) (1 / 2 : ℝ)) errorPositive
  have parameterPositive : 0 < -Real.log (min (target / 2) (1 / 2 : ℝ)) / cutoff :=
    div_pos (neg_pos.mpr (Real.log_neg errorPositive errorBelowOne)) cutoffPositive
  refine ⟨-Real.log (min (target / 2) (1 / 2 : ℝ)) / cutoff, parameterPositive, ?_⟩
  intro index
  have exponentialIdentity :
      Real.exp (-(-Real.log (min (target / 2) (1 / 2 : ℝ)) / cutoff) * cutoff) =
        min (target / 2) (1 / 2 : ℝ) := by
    have exponentIdentity :
        -(-Real.log (min (target / 2) (1 / 2 : ℝ)) / cutoff) * cutoff =
          Real.log (min (target / 2) (1 / 2 : ℝ)) := by
      field_simp
    rw [exponentIdentity, Real.exp_log errorPositive]
  have bound := laplace_le_smallBall measure (measurable index) (nonnegative index)
    parameterPositive.le cutoff
  rw [exponentialIdentity] at bound
  have halfBound := min_le_left (target / 2) (1 / 2 : ℝ)
  linarith [smallBallBound index]

theorem exists_uniform_smallBall_cutoff_of_thinning_bound {Index : Type*}
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (measure : Measure Sample) (value : Index → Sample → ℝ)
    {critical start base cutoff : ℝ}
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (basePositive : 0 < base) (cutoffPositive : 0 < cutoff)
    (tailBound : ∀ index depth,
      measure.real {sample | value index sample ≤ cutoff / base ^ depth} ≤
        (thinningMap network critical)^[depth] start) :
    ∀ error : ℝ, 0 < error → ∃ threshold : ℝ, 0 < threshold ∧
      ∀ index, measure.real {sample | value index sample ≤ threshold} ≤ error := by
  have summability := thinningMap_weighted_iterate_summable network criticalPositive criticalBelowOne
    fixedPoint scale startNonnegative startBelowOne (growth := 1) zero_lt_one
  have convergence : Tendsto (fun depth : ℕ => (thinningMap network critical)^[depth] start)
      atTop (𝓝 0) := by
    simpa only [one_pow, one_mul] using summability.tendsto_atTop_zero
  intro error errorPositive
  obtain ⟨depth, small⟩ := (convergence.eventually (gt_mem_nhds errorPositive)).exists
  exact ⟨cutoff / base ^ depth, div_pos cutoffPositive (pow_pos basePositive depth),
    fun index => (tailBound index depth).trans small.le⟩

/-- The small-ball argument at finite depth.  A common initial probability
strictly below one and the genuine thinning recursion suffice; finite levels
below the requested scale are handled by their deterministic lower bound. -/
theorem finite_depth_thinning_tail_bound
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : ℕ → Sample → ℝ) {critical start base cutoff : ℝ}
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (baseAtLeastOne : 1 ≤ base) (cutoffBelowOne : cutoff < 1)
    (lowerBound : ∀ depth sample, 1 / base ^ depth ≤ value depth sample)
    (initial : ∀ depth, measure.real {sample | value depth sample ≤ cutoff} ≤ start)
    (step : ∀ depth level,
      measure.real {sample | value (depth + 1) sample ≤ cutoff / base ^ (level + 1)} ≤
        thinningMap network critical
          (measure.real {sample | value depth sample ≤ cutoff / base ^ level})) :
    ∀ depth level,
      measure.real {sample | value depth sample ≤ cutoff / base ^ level} ≤
        (thinningMap network critical)^[level] start := by
  have orbitBounds := iterate_bounds startNonnegative startBelowOne
    (thinningMap_zero network critical)
    (fun input nonnegative belowOne => thinningMap_nonnegative network criticalPositive
      criticalBelowOne nonnegative belowOne.le)
    (fun input positive belowOne => thinningMap_strict network criticalPositive criticalBelowOne
      fixedPoint scale positive belowOne)
  apply uniform_finite_depth_tail_le_iterate_on
    (thinningMap_monotoneOn network criticalPositive criticalBelowOne)
    (fun depth => ⟨(orbitBounds depth).1, (orbitBounds depth).2.trans startBelowOne.le⟩)
    (fun depth => (orbitBounds depth).1)
    (fun _ _ => ⟨measureReal_nonneg, measureReal_le_one⟩)
    (by simpa only [pow_zero, div_one] using initial) step
  intro depth level shallow
  have emptyEvent : {sample | value depth sample ≤ cutoff / base ^ level} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro sample within
    have powerComparison : base ^ depth ≤ base ^ level :=
      pow_le_pow_right₀ baseAtLeastOne shallow.le
    have reciprocalComparison : 1 / base ^ level ≤ 1 / base ^ depth :=
      one_div_le_one_div_of_le (pow_pos (zero_lt_one.trans_le baseAtLeastOne) depth)
        powerComparison
    have strictCutoff : cutoff / base ^ level < 1 / base ^ level :=
      (div_lt_div_iff_of_pos_right (pow_pos (zero_lt_one.trans_le baseAtLeastOne) level)).mpr
        cutoffBelowOne
    exact (not_le_of_gt (strictCutoff.trans_le
      (reciprocalComparison.trans (lowerBound depth sample)))) within
  rw [emptyEvent, measureReal_empty]

theorem exists_uniform_laplace_bound_of_finite_depth_thinning
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : ℕ → Sample → ℝ) (measurable : ∀ depth, Measurable (value depth))
    (nonnegative : ∀ depth sample, 0 ≤ value depth sample)
    {critical start base cutoff target : ℝ}
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (baseAtLeastOne : 1 ≤ base) (cutoffPositive : 0 < cutoff) (cutoffBelowOne : cutoff < 1)
    (lowerBound : ∀ depth sample, 1 / base ^ depth ≤ value depth sample)
    (initial : ∀ depth, measure.real {sample | value depth sample ≤ cutoff} ≤ start)
    (step : ∀ depth level,
      measure.real {sample | value (depth + 1) sample ≤ cutoff / base ^ (level + 1)} ≤
        thinningMap network critical
          (measure.real {sample | value depth sample ≤ cutoff / base ^ level}))
    (targetPositive : 0 < target) :
    ∃ parameter : ℝ, 0 < parameter ∧ ∀ depth,
      (∫ sample, Real.exp (-parameter * value depth sample) ∂measure) ≤ target := by
  apply exists_uniform_laplace_bound measure value measurable nonnegative _ targetPositive
  exact exists_uniform_smallBall_cutoff_of_thinning_bound network measure value
    criticalPositive criticalBelowOne fixedPoint scale startNonnegative startBelowOne
    (zero_lt_one.trans_le baseAtLeastOne) cutoffPositive
    (finite_depth_thinning_tail_bound network measure value criticalPositive criticalBelowOne
      fixedPoint scale startNonnegative startBelowOne baseAtLeastOne cutoffBelowOne
      lowerBound initial step)

/-- A uniform second moment supplies the initial small-ball probability in the
finite-depth Laplace estimate.  The remaining probabilistic input is the actual
thinning event recursion. -/
theorem exists_uniform_laplace_bound_of_finite_depth_second_moment
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : ℕ → Sample → ℝ) (measurable : ∀ depth, Measurable (value depth))
    {critical base secondMoment target : ℝ}
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (baseAtLeastOne : 1 ≤ base)
    (lowerBound : ∀ depth sample, 1 / base ^ depth ≤ value depth sample)
    (meanOne : ∀ depth, (∫ sample, value depth sample ∂measure) = 1)
    (squareIntegrable : ∀ depth, Integrable (fun sample => value depth sample ^ 2) measure)
    (secondMomentAtLeastOne : 1 ≤ secondMoment)
    (secondMomentBound : ∀ depth, (∫ sample, value depth sample ^ 2 ∂measure) ≤ secondMoment)
    (step : ∀ depth level,
      measure.real {sample | value (depth + 1) sample ≤ (1 / 2 : ℝ) / base ^ (level + 1)} ≤
        thinningMap network critical
          (measure.real {sample | value depth sample ≤ (1 / 2 : ℝ) / base ^ level}))
    (targetPositive : 0 < target) :
    ∃ parameter : ℝ, 0 < parameter ∧ ∀ depth,
      (∫ sample, Real.exp (-parameter * value depth sample) ∂measure) ≤ target := by
  obtain ⟨start, startNonnegative, startBelowOne, initial⟩ :=
    exists_uniform_smallBall_start_of_second_moment_bound measure value measurable
      (fun depth => integrable_of_integral_eq_one (meanOne depth)) squareIntegrable meanOne
      secondMomentAtLeastOne secondMomentBound
  exact exists_uniform_laplace_bound_of_finite_depth_thinning network measure value measurable
    (fun depth sample => (by positivity : 0 ≤ 1 / base ^ depth).trans (lowerBound depth sample))
    criticalPositive criticalBelowOne fixedPoint scale startNonnegative startBelowOne
    baseAtLeastOne (by norm_num) (by norm_num) lowerBound initial step targetPositive

theorem exists_uniform_inverse_moment_bound_of_finite_depth_second_moment
    {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges)
    (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : ℕ → Sample → ℝ) (measurable : ∀ depth, Measurable (value depth))
    {critical base secondMoment : ℝ}
    (criticalPositive : 0 < critical) (criticalBelowOne : critical < 1)
    (fixedPoint : network.reliability critical = critical)
    (scale : 1 < network.fullGraph.dist network.source network.target)
    (baseAboveOne : 1 < base)
    (lowerBound : ∀ depth sample, 1 / base ^ depth ≤ value depth sample)
    (meanOne : ∀ depth, (∫ sample, value depth sample ∂measure) = 1)
    (squareIntegrable : ∀ depth, Integrable (fun sample => value depth sample ^ 2) measure)
    (secondMomentAtLeastOne : 1 ≤ secondMoment)
    (secondMomentBound : ∀ depth, (∫ sample, value depth sample ^ 2 ∂measure) ≤ secondMoment)
    (step : ∀ depth level,
      measure.real {sample | value (depth + 1) sample ≤ (1 / 2 : ℝ) / base ^ (level + 1)} ≤
        thinningMap network critical
          (measure.real {sample | value depth sample ≤ (1 / 2 : ℝ) / base ^ level})) :
    ∀ power : ℕ, ∃ momentBound : ℝ, ∀ depth,
      (∫ sample, (value depth sample)⁻¹ ^ power ∂measure) ≤ momentBound := by
  obtain ⟨start, startNonnegative, startBelowOne, initial⟩ :=
    exists_uniform_smallBall_start_of_second_moment_bound measure value measurable
      (fun depth => integrable_of_integral_eq_one (meanOne depth)) squareIntegrable meanOne
      secondMomentAtLeastOne secondMomentBound
  have tailBound := finite_depth_thinning_tail_bound network measure value criticalPositive
    criticalBelowOne fixedPoint scale startNonnegative startBelowOne baseAboveOne.le
    (by norm_num : (1 / 2 : ℝ) < 1) lowerBound initial step
  intro power
  refine ⟨(1 / 2 : ℝ)⁻¹ ^ power * (1 + base ^ power *
    ∑' level : ℕ, (base ^ power) ^ level * (thinningMap network critical)^[level] start), ?_⟩
  intro depth
  exact integral_inv_pow_le_of_thinning_tail_bound network measure power (measurable depth)
    (fun sample => (by positivity : 0 < 1 / base ^ depth).trans_le (lowerBound depth sample))
    criticalPositive criticalBelowOne fixedPoint scale startNonnegative startBelowOne
    baseAboveOne (by norm_num) (tailBound depth)

end
end IGSIII.Chemical.SmallBall
