import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology

/-- Weak convergence of actual placed finite probabilities and uniform
convergence of their values imply convergence of the corresponding integrals. -/
theorem uniform_finite_integral_tendsto_completion20261011
    {Space : Type*} [TopologicalSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (Vertex : ℕ → Type*) [∀ depth, Fintype (Vertex depth)]
    [∀ depth, MeasurableSpace (Vertex depth)] [∀ depth, MeasurableSingletonClass (Vertex depth)]
    (measures : ∀ depth, ProbabilityMeasure (Vertex depth)) (limitMeasure : ProbabilityMeasure Space)
    (placement : ∀ depth, Vertex depth → Space)
    (weak : Tendsto (fun depth => (measures depth).map (measurable_of_finite (placement depth)).aemeasurable) atTop (𝓝 limitMeasure))
    (values : ∀ depth, Vertex depth → ℝ) (target : C(Space, ℝ))
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |values depth vertex - target (placement depth vertex)| < tolerance) :
    Tendsto (fun depth => ∫ vertex, values depth vertex ∂(measures depth)) atTop
      (𝓝 (∫ point, target point ∂limitMeasure)) := by
  have fixedConvergence := (ProbabilityMeasure.continuous_integral_continuousMap target).tendsto limitMeasure |>.comp weak
  have fixedIntegral (depth : ℕ) :
      (∫ point, target point ∂((measures depth).map (measurable_of_finite (placement depth)).aemeasurable)) =
      ∫ vertex, target (placement depth vertex) ∂(measures depth) := by
    exact integral_map (measurable_of_finite (placement depth)).aemeasurable target.continuous.aestronglyMeasurable
  have fixedLimit : Tendsto (fun depth => ∫ vertex, target (placement depth vertex) ∂(measures depth)) atTop
      (𝓝 (∫ point, target point ∂limitMeasure)) :=
    fixedConvergence.congr' (Eventually.of_forall fixedIntegral)
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  have halfPositive : 0 < tolerance / 2 := by positivity
  filter_upwards [uniform (tolerance / 2) halfPositive,
    fixedLimit.eventually (Metric.ball_mem_nhds _ halfPositive)] with depth close fixedClose
  have integralError : |(∫ vertex, values depth vertex ∂(measures depth)) -
      ∫ vertex, target (placement depth vertex) ∂(measures depth)| ≤ tolerance / 2 := by
    rw [← integral_sub Integrable.of_finite Integrable.of_finite]
    have estimate := norm_integral_le_of_norm_le_const (μ := (measures depth : Measure (Vertex depth)))
      (f := fun vertex => values depth vertex - target (placement depth vertex))
      (C := tolerance / 2) (Eventually.of_forall fun vertex => by
        simpa only [Real.norm_eq_abs] using (close vertex).le)
    simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using estimate
  rw [Real.dist_eq] at fixedClose
  rw [Real.dist_eq]
  exact (abs_sub_le _ _ _).trans_lt (by linarith)

end
end IGSIII34.Diffusion
