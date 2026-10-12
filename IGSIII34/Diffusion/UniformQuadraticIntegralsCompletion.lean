import IGSIII34.Diffusion.UniformFiniteIntegralCompletion
import IGSIII34.Diffusion.FiniteResolventMinimumCompletion
import IGSIII34.Diffusion.StationaryDegreeWalkCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology BigOperators

/-- Uniformly converging finite potentials also converge uniformly after
squaring, because the genuine continuous limiting potential is bounded. -/
theorem uniform_finite_square_completion
    {Space : Type*} [TopologicalSpace Space] [CompactSpace Space]
    (Vertex : ℕ → Type*) (placement : ∀ depth, Vertex depth → Space)
    (values : ∀ depth, Vertex depth → ℝ) (target : C(Space, ℝ))
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |values depth vertex - target (placement depth vertex)| < tolerance) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |values depth vertex ^ 2 - target (placement depth vertex) ^ 2| < tolerance := by
  intro tolerance positive
  let bound : ℝ := ‖target‖
  have boundNonnegative : 0 ≤ bound := norm_nonneg target
  have factorPositive : 0 < 2 * bound + 1 := by positivity
  filter_upwards [uniform (min 1 (tolerance / (2 * bound + 1))) (lt_min (by norm_num) (by positivity))]
    with depth close
  intro vertex
  have differenceSmall : |values depth vertex - target (placement depth vertex)| < 1 := (close vertex).trans_le (min_le_left _ _)
  have differenceError : |values depth vertex - target (placement depth vertex)| < tolerance / (2 * bound + 1) :=
    (close vertex).trans_le (min_le_right _ _)
  have targetBound : |target (placement depth vertex)| ≤ bound := by
    simpa only [Real.norm_eq_abs] using target.norm_coe_le_norm (placement depth vertex)
  have valueBound : |values depth vertex| < bound + 1 := by
    have triangle := abs_add_le (values depth vertex - target (placement depth vertex)) (target (placement depth vertex))
    rw [sub_add_cancel] at triangle
    linarith
  have sumBound : |values depth vertex + target (placement depth vertex)| ≤ 2 * bound + 1 := by
    have triangle := abs_add_le (values depth vertex) (target (placement depth vertex))
    linarith
  have factor : values depth vertex ^ 2 - target (placement depth vertex) ^ 2 =
      (values depth vertex - target (placement depth vertex)) * (values depth vertex + target (placement depth vertex)) := by ring
  rw [factor, abs_mul]
  exact (mul_le_mul_of_nonneg_left sumBound (abs_nonneg _)).trans_lt
    ((mul_lt_mul_of_pos_right differenceError factorPositive).trans_eq (div_mul_cancel₀ tolerance (ne_of_gt factorPositive)))

/-- The forcing term uses the actual placed continuous forcing, so no
independent forcing-convergence assumption is needed. -/
theorem uniform_finite_forcing_product_completion
    {Space : Type*} [TopologicalSpace Space] [CompactSpace Space]
    (Vertex : ℕ → Type*) (placement : ∀ depth, Vertex depth → Space)
    (values : ∀ depth, Vertex depth → ℝ) (target forcing : C(Space, ℝ))
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |values depth vertex - target (placement depth vertex)| < tolerance) :
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |forcing (placement depth vertex) * values depth vertex -
        forcing (placement depth vertex) * target (placement depth vertex)| < tolerance := by
  intro tolerance positive
  have boundNonnegative := norm_nonneg forcing
  have factorPositive : 0 < ‖forcing‖ + 1 := by positivity
  filter_upwards [uniform (tolerance / (‖forcing‖ + 1)) (by positivity)] with depth close
  intro vertex
  have forcingBound : |forcing (placement depth vertex)| ≤ ‖forcing‖ := by
    simpa only [Real.norm_eq_abs] using forcing.norm_coe_le_norm (placement depth vertex)
  rw [← mul_sub, abs_mul]
  have factorBound : |forcing (placement depth vertex)| ≤ ‖forcing‖ + 1 := by linarith
  exact (mul_le_mul_of_nonneg_right factorBound (abs_nonneg _)).trans_lt
    ((mul_lt_mul_of_pos_left (close vertex) factorPositive).trans_eq (mul_div_cancel₀ tolerance (ne_of_gt factorPositive)))

/-- The mass and forcing portions of the full finite variational objective
converge under the genuine placed probability and uniform potential limits. -/
theorem uniform_finite_quadratic_integrals_completion
    {Space : Type*} [TopologicalSpace Space] [CompactSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (Vertex : ℕ → Type*) [∀ depth, Fintype (Vertex depth)]
    [∀ depth, MeasurableSpace (Vertex depth)] [∀ depth, MeasurableSingletonClass (Vertex depth)]
    (measures : ∀ depth, ProbabilityMeasure (Vertex depth)) (limitMeasure : ProbabilityMeasure Space)
    (placement : ∀ depth, Vertex depth → Space)
    (weak : Tendsto (fun depth => (measures depth).map (measurable_of_finite (placement depth)).aemeasurable) atTop (𝓝 limitMeasure))
    (values : ∀ depth, Vertex depth → ℝ) (target forcing : C(Space, ℝ))
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, |values depth vertex - target (placement depth vertex)| < tolerance) :
    Tendsto (fun depth => ∫ vertex, values depth vertex ^ 2 ∂(measures depth)) atTop
      (𝓝 (∫ point, target point ^ 2 ∂limitMeasure)) ∧
    Tendsto (fun depth => ∫ vertex, forcing (placement depth vertex) * values depth vertex ∂(measures depth)) atTop
      (𝓝 (∫ point, forcing point * target point ∂limitMeasure)) := by
  constructor
  · exact uniform_finite_integral_tendsto_completion Vertex measures limitMeasure placement weak
      (fun depth vertex => values depth vertex ^ 2) (target ^ 2)
      (uniform_finite_square_completion Vertex placement values target uniform)
  · exact uniform_finite_integral_tendsto_completion Vertex measures limitMeasure placement weak
      (fun depth vertex => forcing (placement depth vertex) * values depth vertex) (forcing * target)
      (uniform_finite_forcing_product_completion Vertex placement values target forcing uniform)

end
end IGSIII34.Diffusion

