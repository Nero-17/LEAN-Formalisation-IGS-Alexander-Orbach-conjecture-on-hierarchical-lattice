import IGSIII34.Percolation.PhysicalInverse
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology ENNReal NNReal

theorem abs_log_le_self_add_inverse {value : ℝ} (nonnegative : 0 ≤ value) :
    |Real.log value| ≤ value + value⁻¹ := by
  rw [abs_le]
  exact ⟨by linarith [Real.neg_inv_le_log nonnegative],
    (Real.log_le_self nonnegative).trans (le_add_of_nonneg_right (inv_nonneg.mpr nonnegative))⟩

theorem log_sq_le_positive_inverse_squares {value : ℝ} (nonnegative : 0 ≤ value) :
    (Real.log value)^2 ≤ 2 * (value^2 + (value⁻¹)^2) := by
  have bound := abs_log_le_self_add_inverse nonnegative
  have inverseNonnegative := inv_nonneg.mpr nonnegative
  have squared := mul_self_le_mul_self (abs_nonneg _) bound
  nlinarith [sq_nonneg (value-value⁻¹), sq_abs (Real.log value)]

theorem uniform_log_second_moment
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (value : ℕ → Sample → ℝ) (measurable : ∀ depth, Measurable (value depth))
    (nonnegative : ∀ depth sample, 0 ≤ value depth sample)
    (positiveMoment inverseMoment : ℝ)
    (positiveBound : ∀ depth, Integrable (fun sample => (value depth sample)^2) measure ∧
      (∫ sample, (value depth sample)^2 ∂measure) ≤ positiveMoment)
    (inverseBound : ∀ depth, Integrable (fun sample => ((value depth sample)⁻¹)^2) measure ∧
      (∫ sample, ((value depth sample)⁻¹)^2 ∂measure) ≤ inverseMoment) :
    ∀ depth, Integrable (fun sample => (Real.log (value depth sample))^2) measure ∧
      (∫ sample, (Real.log (value depth sample))^2 ∂measure) ≤ 2*(positiveMoment+inverseMoment) := by
  intro depth
  have domination := ((positiveBound depth).1.add (inverseBound depth).1).const_mul 2
  have integrable : Integrable (fun sample => (Real.log (value depth sample))^2) measure := by
    apply domination.mono' ((measurable depth).log.pow_const 2).aestronglyMeasurable
    filter_upwards with sample
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (value depth sample)))]
    exact
      log_sq_le_positive_inverse_squares (nonnegative depth sample)
  refine ⟨integrable, ?_⟩
  calc
    _ ≤ ∫ sample, 2*((value depth sample)^2+((value depth sample)⁻¹)^2) ∂measure :=
      integral_mono integrable domination (fun sample => log_sq_le_positive_inverse_squares (nonnegative depth sample))
    _ = 2*((∫ sample, (value depth sample)^2 ∂measure)+(∫ sample, ((value depth sample)⁻¹)^2 ∂measure)) := by
      rw [integral_const_mul, integral_add (positiveBound depth).1 (inverseBound depth).1]
    _ ≤ _ := by linarith [(positiveBound depth).2, (inverseBound depth).2]

theorem summable_nat_inverse_square : Summable (fun depth : ℕ => 1 / (depth : ℝ)^2) := by
  apply (summable_nat_add_iff 1).mp
  apply summable_of_sum_range_le (fun _ => by positivity) (c := 2)
  intro count
  have stronger : ∑ depth ∈ Finset.range count, 1 / ((depth+1 : ℕ) : ℝ)^2 ≤ 2 - 2 / ((count+1 : ℕ) : ℝ) := by
    induction count with
    | zero => norm_num
    | succ count previous =>
      rw [Finset.sum_range_succ]
      have firstPositive : (0 : ℝ) < ((count+1 : ℕ) : ℝ) := by positivity
      have secondPositive : (0 : ℝ) < ((count+2 : ℕ) : ℝ) := by positivity
      have step : 1 / ((count+1 : ℕ) : ℝ)^2 ≤
          2 / ((count+1 : ℕ) : ℝ) - 2 / ((count+2 : ℕ) : ℝ) := by
        calc
          _ ≤ 2 / (((count+1 : ℕ) : ℝ) * ((count+2 : ℕ) : ℝ)) := by
            apply (div_le_div_iff₀ (sq_pos_of_pos firstPositive) (mul_pos firstPositive secondPositive)).mpr
            push_cast
            nlinarith [Nat.cast_nonneg (α := ℝ) count]
          _ = _ := by
            push_cast
            field_simp
            ring
      have index : count+1+1=count+2 := by omega
      rw [index]
      linarith
  exact stronger.trans (sub_le_self _ (by positivity))

theorem ae_log_div_nat_tendsto_zero_of_uniform_second_moment
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (value : ℕ → Sample → ℝ) (measurable : ∀ depth, Measurable (value depth))
    (bound : ℝ)
    (moments : ∀ depth, Integrable (fun sample => (Real.log (value depth sample))^2) measure ∧
      (∫ sample, (Real.log (value depth sample))^2 ∂measure) ≤ bound) :
    ∀ᵐ sample ∂measure, Tendsto (fun depth : ℕ => Real.log (value depth sample) / depth) atTop (𝓝 0) := by
  have integralBound (depth : ℕ) :
      eLpNorm (fun sample => (Real.log (value depth sample)/(depth : ℝ))^2) 1 measure ≤
        ENNReal.ofReal (bound / (depth : ℝ)^2) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    simp_rw [Real.enorm_of_nonneg (sq_nonneg _)]
    simp_rw [div_pow]
    rw [← ofReal_integral_eq_lintegral_ofReal ((moments depth).1.div_const ((depth : ℝ)^2))]
    · apply ENNReal.ofReal_le_ofReal
      rw [integral_div]
      exact div_le_div_of_nonneg_right (moments depth).2 (sq_nonneg _)
    · filter_upwards with sample
      positivity
  have summableBounds : Summable (fun depth : ℕ => bound / (depth : ℝ)^2) := by
    simpa only [mul_one_div] using summable_nat_inverse_square.mul_left bound
  have finiteNorms : ∑' depth, eLpNorm (fun sample => (Real.log (value depth sample)/(depth : ℝ))^2) 1 measure ≠ ∞ :=
    ne_top_of_le_ne_top summableBounds.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum integralBound)
  have summable := summable_norm_of_tsum_eLpNorm_ne_top (μ := measure) (p := 1) le_rfl
    (fun depth => ((measurable depth).log.div_const (depth : ℝ)).pow_const 2 |>.aestronglyMeasurable) finiteNorms
  filter_upwards [summable] with sample sampleSummable
  have squareLimit : Tendsto (fun depth : ℕ => (Real.log (value depth sample)/(depth : ℝ))^2) atTop (𝓝 0) := by
    have limit := sampleSummable.tendsto_atTop_zero
    simp only [Real.norm_eq_abs] at limit
    simp_rw [abs_of_nonneg (sq_nonneg (Real.log (value _ sample)/(_ : ℝ)))] at limit
    exact limit
  have absoluteLimit : Tendsto (fun depth : ℕ => |Real.log (value depth sample)/(depth : ℝ)|) atTop (𝓝 0) := by
    have result := Real.continuous_sqrt.continuousAt.tendsto.comp squareLimit
    change Tendsto (fun depth : ℕ => Real.sqrt ((Real.log (value depth sample)/(depth : ℝ))^2)) atTop (𝓝 (Real.sqrt 0)) at result
    simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero] using result
  have negativeLimit : Tendsto (fun depth : ℕ => -|Real.log (value depth sample)/(depth : ℝ)|) atTop (𝓝 0) := by
    simpa only [neg_zero] using absoluteLimit.neg
  exact negativeLimit.squeeze' absoluteLimit
    (Filter.Eventually.of_forall (fun _ => neg_abs_le _))
    (Filter.Eventually.of_forall (fun _ => le_abs_self _))

theorem tendsto_div_nat_of_bounded (value : ℕ → ℝ) (bound : ℝ)
    (bounded : ∀ depth, |value depth| ≤ bound) :
    Tendsto (fun depth : ℕ => value depth / depth) atTop (𝓝 0) := by
  have absoluteBound (depth : ℕ) : |value depth/(depth : ℝ)| ≤ bound/(depth : ℝ) := by
    rw [abs_div, show |(depth : ℝ)| = (depth : ℝ) from abs_of_nonneg (Nat.cast_nonneg depth)]
    exact div_le_div_of_nonneg_right (bounded depth) (Nat.cast_nonneg depth)
  have upperLimit : Tendsto (fun depth : ℕ => bound/(depth : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat bound
  have lowerLimit : Tendsto (fun depth : ℕ => -(bound/(depth : ℝ))) atTop (𝓝 0) := by
    simpa only [neg_zero] using upperLimit.neg
  exact lowerLimit.squeeze' upperLimit
    (Eventually.of_forall (fun depth => (abs_le.mp (absoluteBound depth)).1))
    (Eventually.of_forall (fun depth => (abs_le.mp (absoluteBound depth)).2))

theorem tendsto_log_div_nat_of_growth_bounds (value : ℕ → ℝ) (growth constant : ℝ)
    (growthPositive : 0 < growth) (constantAtLeastOne : 1 ≤ constant)
    (bounds : ∀ depth, growth^depth ≤ value depth ∧ value depth ≤ constant*growth^depth) :
    Tendsto (fun depth : ℕ => Real.log (value depth)/depth) atTop (𝓝 (Real.log growth)) := by
  have constantPositive := zero_lt_one.trans_le constantAtLeastOne
  have differenceBound (depth : ℕ) : |Real.log (value depth) - (depth : ℝ)*Real.log growth| ≤ Real.log constant := by
    have valuePositive := (pow_pos growthPositive depth).trans_le (bounds depth).1
    have lower := Real.log_le_log (pow_pos growthPositive depth) (bounds depth).1
    have upper := Real.log_le_log valuePositive (bounds depth).2
    rw [Real.log_pow] at lower
    rw [Real.log_mul constantPositive.ne' (pow_pos growthPositive depth).ne', Real.log_pow] at upper
    rw [abs_le]
    constructor <;> linarith [Real.log_nonneg constantAtLeastOne]
  have residueLimit := tendsto_div_nat_of_bounded
    (fun depth => Real.log (value depth)-(depth : ℝ)*Real.log growth) (Real.log constant) differenceBound
  have result : Tendsto (fun depth : ℕ => Real.log growth +
      (Real.log (value depth)-(depth : ℝ)*Real.log growth)/(depth : ℝ)) atTop (𝓝 (Real.log growth)) := by
    simpa only [add_zero] using tendsto_const_nhds.add residueLimit
  apply result.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with depth depthPositive
  have depthNonzero : (depth : ℝ) ≠ 0 := by exact_mod_cast depthPositive.ne'
  field_simp
  ring

theorem integral_log_abs_bound_of_second_moment
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample) [IsProbabilityMeasure measure]
    (value : Sample → ℝ) (measurable : Measurable value)
    (integrableSquare : Integrable (fun sample => (Real.log (value sample))^2) measure) :
    Integrable (fun sample => Real.log (value sample)) measure ∧
      |∫ sample, Real.log (value sample) ∂measure| ≤ 1 + ∫ sample, (Real.log (value sample))^2 ∂measure := by
  have pointwise (sample : Sample) : |Real.log (value sample)| ≤ 1 + (Real.log (value sample))^2 := by
    nlinarith [sq_nonneg (|Real.log (value sample)|-1), sq_abs (Real.log (value sample))]
  have domination := (integrable_const (μ := measure) (1 : ℝ)).add integrableSquare
  have integrable : Integrable (fun sample => Real.log (value sample)) measure := by
    apply domination.mono' measurable.log.aestronglyMeasurable
    filter_upwards with sample
    change |Real.log (value sample)| ≤ 1 + (Real.log (value sample))^2
    exact pointwise sample
  refine ⟨integrable, (abs_integral_le_integral_abs).trans ?_⟩
  calc
    _ ≤ ∫ sample, 1 + (Real.log (value sample))^2 ∂measure :=
      integral_mono integrable.abs domination pointwise
    _ = _ := by rw [integral_add (integrable_const _) integrableSquare]; simp

end
end IGSIII34.Probability
