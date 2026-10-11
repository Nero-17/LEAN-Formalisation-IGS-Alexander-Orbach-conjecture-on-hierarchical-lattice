import Universality.Analysis.DiscountedIteration
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

namespace Universality
noncomputable section
open Filter
open scoped Topology

/-- A bounded observable satisfying an asymptotically homogeneous contraction
must vanish. This is a filter statement, so no quantitative escape-time estimate
is required to apply it to critical limits. -/
theorem tendsto_zero_of_local_renormalization {space : Type*} (filter : Filter space)
    (iteration : space → space) (observable error : space → ℝ) (contraction bound : ℝ)
    (hcontraction : 0 ≤ contraction) (hcontractionOne : contraction < 1)
    (hiteration : Tendsto iteration filter filter)
    (hbound : ∀ᶠ point in filter, |observable point| ≤ bound)
    (herror : Tendsto error filter (𝓝 0))
    (hrecursion : ∀ᶠ point in filter,
      |observable point| ≤ contraction * |observable (iteration point)| + |error point|) :
    Tendsto observable filter (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro epsilon hepsilon
  have herrorAbs : Tendsto (fun point => |error point|) filter (𝓝 0) := by simpa using herror.abs
  have hsmallError : ∀ᶠ point in filter,
      |error point| ≤ epsilon * (1 - contraction) / 2 := by
    have hpositive : 0 < epsilon * (1 - contraction) / 2 := by positivity
    filter_upwards [herrorAbs.eventually (gt_mem_nhds hpositive)] with point hp
    exact hp.le
  have hiterated (n : ℕ) : ∀ᶠ point in filter,
      |observable point| ≤ contraction ^ n * bound + epsilon / 2 := by
    induction n with
    | zero =>
      filter_upwards [hbound] with point hp
      simp only [pow_zero, one_mul]
      linarith
    | succ n ih =>
      filter_upwards [hrecursion, hsmallError, hiteration.eventually ih] with point hr he hi
      have hscaled := mul_le_mul_of_nonneg_left hi hcontraction
      rw [pow_succ]
      nlinarith
  have hpowers : Tendsto (fun n : ℕ => contraction ^ n * bound) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hcontraction hcontractionOne).mul_const bound
  obtain ⟨n, hn⟩ := (hpowers.eventually (gt_mem_nhds (show 0 < epsilon / 2 by positivity))).exists
  filter_upwards [hiterated n] with point hp
  rw [Real.dist_eq, sub_zero]
  linarith

/-- A uniform bound propagates backward from the first exit as soon as the
response coefficient is smaller than the renormalization multiplier. -/
theorem bounded_response_from_finite_exit {space : Type*}
    (iteration : space → space) (observable deviation : space → ℝ)
    (radius contraction forcing bound : ℝ)
    (hcontraction : 0 ≤ contraction) (hbalance : contraction * bound + forcing ≤ bound)
    (houtside : ∀ point, radius ≤ |deviation point| → |observable point| ≤ bound)
    (hrecursion : ∀ point, |deviation point| < radius →
      |observable point| ≤ contraction * |observable (iteration point)| + forcing)
    (point : space) (depth : ℕ) (hexit : radius ≤ |deviation (iteration^[depth] point)|) :
    |observable point| ≤ bound := by
  induction depth generalizing point with
  | zero => exact houtside point (by simpa using hexit)
  | succ depth ih =>
    by_cases hout : radius ≤ |deviation point|
    · exact houtside point hout
    have hnext := ih (iteration point)
      (by simpa only [Function.iterate_succ_apply] using hexit)
    exact (hrecursion point (lt_of_not_ge hout)).trans
      ((add_le_add (mul_le_mul_of_nonneg_left hnext hcontraction) le_rfl).trans hbalance)

end
end Universality

