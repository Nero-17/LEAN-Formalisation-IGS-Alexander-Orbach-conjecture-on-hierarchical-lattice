import IGSIII34.Diffusion.CountableTimeLimitsCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology

/-- A true countable observation-law limit preserves paired cylinder
moments of genuine uniformly converging correctors. The sample laws may be
infinite path laws; no finite-dimensional or continuous-path premise is hidden. -/
theorem observed_corrector_paired_integral_tendsto_completion
    {Space : Type*} [MetricSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (Samples : ℕ → Type*) [∀ depth, MeasurableSpace (Samples depth)]
    (laws : ∀ depth, ProbabilityMeasure (Samples depth))
    (observations : ∀ depth, Samples depth → (ℕ → Space)) (observationsMeasurable : ∀ depth, Measurable (observations depth))
    (limitLaw : ProbabilityMeasure (ℕ → Space))
    (weak : Tendsto (fun depth => (laws depth).map (observationsMeasurable depth).aemeasurable) atTop (𝓝 limitLaw))
    {count : ℕ} (coordinates : Fin count → ℕ) (future : ℕ)
    (past : C((Fin count → Space), ℝ)) (target : C(Space, ℝ))
    (correctors : ∀ depth, Samples depth → ℝ)
    (integrable : ∀ depth, Integrable (fun sample => past (fun index => observations depth sample (coordinates index)) * correctors depth sample) (laws depth))
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ sample, |correctors depth sample - target (observations depth sample future)| < tolerance) :
    Tendsto (fun depth => ∫ sample, past (fun index => observations depth sample (coordinates index)) * correctors depth sample ∂(laws depth)) atTop
      (𝓝 (∫ path : ℕ → Space, past (fun index => path (coordinates index)) * target (path future) ∂limitLaw)) := by
  let test : C((ℕ → Space), ℝ) := ⟨fun path => past (fun index => path (coordinates index)) * target (path future), by fun_prop⟩
  have fixedLimit := (ProbabilityMeasure.continuous_integral_continuousMap test).tendsto limitLaw |>.comp weak
  have mappedIntegral (depth : ℕ) : (∫ path, test path ∂((laws depth).map (observationsMeasurable depth).aemeasurable)) =
      ∫ sample, test (observations depth sample) ∂(laws depth) :=
    integral_map (observationsMeasurable depth).aemeasurable test.continuous.aestronglyMeasurable
  have fixedConvergence : Tendsto (fun depth => ∫ sample, test (observations depth sample) ∂(laws depth)) atTop
      (𝓝 (∫ path, test path ∂limitLaw)) := fixedLimit.congr' (Eventually.of_forall mappedIntegral)
  have fixedIntegrable (depth : ℕ) : Integrable (fun sample => test (observations depth sample)) (laws depth) := by
    apply (MemLp.of_bound ((test.continuous.measurable.comp (observationsMeasurable depth)).aestronglyMeasurable)
      ‖test‖ (Eventually.of_forall fun sample => test.norm_coe_le_norm (observations depth sample)) (p := 1)).integrable le_rfl
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  have halfPositive : 0 < tolerance / 2 := by positivity
  have denominatorPositive : 0 < ‖past‖ + 1 := by positivity
  filter_upwards [uniform ((tolerance / 2) / (‖past‖ + 1)) (by positivity),
    fixedConvergence.eventually (Metric.ball_mem_nhds _ halfPositive)] with depth close fixedClose
  have pairedIntegrandBound (sample : Samples depth) :
      |past (fun index => observations depth sample (coordinates index)) * correctors depth sample - test (observations depth sample)| ≤ tolerance / 2 := by
    change |past (fun index => observations depth sample (coordinates index)) * correctors depth sample -
      past (fun index => observations depth sample (coordinates index)) * target (observations depth sample future)| ≤ tolerance / 2
    rw [← mul_sub, abs_mul]
    have pastBound : |past (fun index => observations depth sample (coordinates index))| ≤ ‖past‖ + 1 := by
      have bound := past.norm_coe_le_norm (fun index => observations depth sample (coordinates index))
      rw [Real.norm_eq_abs] at bound
      linarith
    exact (mul_le_mul_of_nonneg_right pastBound (abs_nonneg _)).trans
      ((mul_le_mul_of_nonneg_left (close sample).le denominatorPositive.le).trans_eq
        (mul_div_cancel₀ (tolerance / 2) denominatorPositive.ne'))
  have integralError : |(∫ sample, past (fun index => observations depth sample (coordinates index)) * correctors depth sample ∂(laws depth)) -
      ∫ sample, test (observations depth sample) ∂(laws depth)| ≤ tolerance / 2 := by
    rw [← integral_sub (integrable depth) (fixedIntegrable depth)]
    have bound := norm_integral_le_of_norm_le_const (μ := (laws depth : Measure (Samples depth)))
      (f := fun sample => past (fun index => observations depth sample (coordinates index)) * correctors depth sample - test (observations depth sample))
      (C := tolerance / 2) (Eventually.of_forall fun sample => by
        simpa only [Real.norm_eq_abs] using pairedIntegrandBound sample)
    simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using bound
  rw [Real.dist_eq] at fixedClose
  rw [Real.dist_eq]
  change |(∫ sample, past (fun index => observations depth sample (coordinates index)) * correctors depth sample ∂(laws depth)) - ∫ path, test path ∂limitLaw| < tolerance
  exact (abs_sub_le _ (∫ sample, test (observations depth sample) ∂(laws depth)) _).trans_lt (by linarith)

end
end IGSIII34.Diffusion




