import Universality.Analysis.GeometricSumLogRate
import Universality.Analysis.StoppedGeometricLogBound
import Universality.Analysis.PowerBoundsFromLogError

namespace Universality
noncomputable section

/-- In the growing geometric regime, bounded escape-time error gives
uniform two-constant power bounds, not merely a logarithmic exponent. -/
theorem stopped_geometric_power_comparison (ratio multiplier lower upper bound : ℝ)
    (hratio : 1 < ratio) (hmultiplier : 1 < multiplier)
    (hlower : 0 < lower) (hupper : 0 < upper) :
    ∃ first last : ℝ, 0 < first ∧ 0 < last ∧
      ∀ depth : ℕ, 1 ≤ depth → ∀ deviation response : ℝ, 0 < deviation →
      lower * (∑ n ∈ Finset.range depth, ratio ^ (n + 1)) ≤ response →
      response ≤ upper * (∑ n ∈ Finset.range depth, ratio ^ (n + 1)) →
      |(depth : ℝ) * Real.log multiplier + Real.log deviation| ≤ bound →
      first * deviation ^ (-Real.log ratio / Real.log multiplier) ≤ response ∧
        response ≤ last * deviation ^ (-Real.log ratio / Real.log multiplier) := by
  have hratioPos : 0 < ratio := zero_lt_one.trans hratio
  have hlog : 0 < Real.log multiplier := Real.log_pos hmultiplier
  let error : ℝ := |Real.log lower| + |Real.log (upper * (ratio / (ratio - 1)))| +
    |Real.log ratio / Real.log multiplier| * bound
  refine ⟨Real.exp (-error), Real.exp error, Real.exp_pos _, Real.exp_pos _, ?_⟩
  intro depth hdepth deviation response hdeviation hresponseLower hresponseUpper hescape
  have hsum := geometric_sum_from_one_bounds_above_one ratio hratio depth hdepth
  have hl : lower * ratio ^ depth ≤ response :=
    (mul_le_mul_of_nonneg_left hsum.1 hlower.le).trans hresponseLower
  have hu : response ≤ (upper * (ratio / (ratio - 1))) * ratio ^ depth := by
    calc
      response ≤ upper * (∑ n ∈ Finset.range depth, ratio ^ (n + 1)) := hresponseUpper
      _ ≤ upper * ((ratio / (ratio - 1)) * ratio ^ depth) :=
        mul_le_mul_of_nonneg_left hsum.2 hupper.le
      _ = _ := by ring
  have hresponse : 0 < response := (mul_pos hlower (pow_pos hratioPos _)).trans_le hl
  have hmass := log_error_of_geometric_comparison response ratio lower
    (upper * (ratio / (ratio - 1))) depth hratioPos hlower
    (mul_pos hupper (div_pos hratioPos (sub_pos.mpr hratio))) hl hu
  have herror : |Real.log response - (-Real.log ratio / Real.log multiplier) * Real.log deviation| ≤ error := by
    have heq : Real.log response - (-Real.log ratio / Real.log multiplier) * Real.log deviation =
        (Real.log response - (depth : ℝ) * Real.log ratio) +
          (Real.log ratio / Real.log multiplier) *
            ((depth : ℝ) * Real.log multiplier + Real.log deviation) := by
      field_simp [hlog.ne']
      <;> ring
    rw [heq]
    calc
      _ ≤ |Real.log response - (depth : ℝ) * Real.log ratio| +
          |(Real.log ratio / Real.log multiplier) *
            ((depth : ℝ) * Real.log multiplier + Real.log deviation)| := abs_add_le _ _
      _ ≤ error := by
        rw [abs_mul]
        exact add_le_add hmass (mul_le_mul_of_nonneg_left hescape (abs_nonneg _))
  exact rpow_bounds_of_log_error response deviation _ error hresponse hdeviation herror

/-- In the ratio-one regime the stopped sum is the exit depth, and is
therefore comparable to minus the logarithm of the deviation. -/
theorem stopped_linear_log_comparison (multiplier lower upper : ℝ)
    (hmultiplier : 1 < multiplier) (hlower : 0 < lower) (hupper : 0 < upper) :
    ∃ first last : ℝ, 0 < first ∧ 0 < last ∧
      ∀ depth : ℕ, ∀ deviationLog response bound : ℝ,
      lower * depth ≤ response → response ≤ upper * depth →
      |(depth : ℝ) * Real.log multiplier + deviationLog| ≤ bound → deviationLog ≤ -2 * bound →
      first * (-deviationLog) ≤ response ∧ response ≤ last * (-deviationLog) := by
  have hlog : 0 < Real.log multiplier := Real.log_pos hmultiplier
  have hdenom : 0 < 2 * Real.log multiplier := mul_pos (by norm_num) hlog
  refine ⟨lower / (2 * Real.log multiplier), (3 * upper) / (2 * Real.log multiplier),
    div_pos hlower hdenom, div_pos (mul_pos (by norm_num) hupper) hdenom, ?_⟩
  intro depth deviationLog response bound hl hu hescape hsmall
  obtain ⟨hescapeLower, hescapeUpper⟩ := abs_le.mp hescape
  have hdepthLower : -deviationLog / (2 * Real.log multiplier) ≤ (depth : ℝ) :=
    (div_le_iff₀ hdenom).mpr (by nlinarith only [hescapeLower, hsmall])
  have hdepthUpper : (depth : ℝ) ≤ (3 * -deviationLog) / (2 * Real.log multiplier) :=
    (le_div_iff₀ hdenom).mpr (by nlinarith only [hescapeUpper, hsmall])
  constructor
  · calc
      _ = lower * (-deviationLog / (2 * Real.log multiplier)) := by ring
      _ ≤ lower * depth := mul_le_mul_of_nonneg_left hdepthLower hlower.le
      _ ≤ response := hl
  · calc
      response ≤ upper * depth := hu
      _ ≤ upper * ((3 * -deviationLog) / (2 * Real.log multiplier)) :=
        mul_le_mul_of_nonneg_left hdepthUpper hupper.le
      _ = _ := by ring

end
end Universality
