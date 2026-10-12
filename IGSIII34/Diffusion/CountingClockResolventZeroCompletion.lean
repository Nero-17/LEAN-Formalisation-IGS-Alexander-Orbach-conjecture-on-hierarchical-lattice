import IGSIII34.Diffusion.CountingClockDensityCompletion
import IGSIII34.Diffusion.UniformQuadraticIntegralsCompletion
import IGSIII34.Diffusion.FiniteResolventMinimumCompletion
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped _root_.Topology BigOperators
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space] [MeasurableSpace Space] [BorelSpace Space]

theorem countingClockResolvent_uniform_limit_zero_completion
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)] [∀ depth, DecidableEq (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)]
    [∀ depth, Nonempty (Vertices depth)] [∀ depth, Fintype (Edges depth)] [∀ depth, Nonempty (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (parameter : ℝ) (parameterPositive : 0 < parameter) (scale : ℕ → ℝ) (scaleNonnegative : ∀ depth, 0 ≤ scale depth)
    (measure : ProbabilityMeasure Space) [(measure : Measure Space).IsOpenPosMeasure]
    (placement : ∀ depth, Vertices depth → Space)
    (degreeWeak : Tendsto (fun depth => ProbabilityMeasure.map (⟨degreeMeasure (endpoint depth), inferInstance⟩ : ProbabilityMeasure (Vertices depth))
      (measurable_of_finite (placement depth)).aemeasurable) atTop (𝓝 measure))
    (countingWeak : Tendsto (fun depth => ProbabilityMeasure.map (⟨uniformOn Set.univ, inferInstance⟩ : ProbabilityMeasure (Vertices depth))
      (measurable_of_finite (placement depth)).aemeasurable) atTop (𝓝 measure))
    (target : C(Space, ℝ))
    (uniform : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
      |finiteGraphResolvent (endpoint depth) (positiveDegree depth) parameter
        (2 * Fintype.card (Edges depth) * scale depth) parameterPositive (mul_nonneg (by positivity) (scaleNonnegative depth))
        (fun vertex => finiteCountingClockDensityCompletion (endpoint depth) vertex - 1) vertex -
        target (placement depth vertex)| < tolerance) : target = 0 := by
  let values := fun depth => finiteGraphResolvent (endpoint depth) (positiveDegree depth) parameter
    (2 * Fintype.card (Edges depth) * scale depth) parameterPositive (mul_nonneg (by positivity) (scaleNonnegative depth))
    (fun vertex => finiteCountingClockDensityCompletion (endpoint depth) vertex - 1)
  let degrees := fun depth => (⟨degreeMeasure (endpoint depth), inferInstance⟩ : ProbabilityMeasure (Vertices depth))
  let counts := fun depth => (⟨uniformOn Set.univ, inferInstance⟩ : ProbabilityMeasure (Vertices depth))
  have degreeIntegral := uniform_finite_integral_tendsto_completion Vertices degrees measure placement degreeWeak values target uniform
  have countIntegral := uniform_finite_integral_tendsto_completion Vertices counts measure placement countingWeak values target uniform
  have centeredIntegral : Tendsto (fun depth => ∫ vertex,
      (finiteCountingClockDensityCompletion (endpoint depth) vertex - 1) * values depth vertex ∂degreeMeasure (endpoint depth)) atTop (𝓝 (0 : ℝ)) := by
    have difference := countIntegral.sub degreeIntegral
    simp only [sub_self] at difference
    exact difference.congr' (Eventually.of_forall fun depth => (finiteCenteredCountingClock_integral_completion
      (endpoint depth) (positiveDegree depth) (values depth)).symm)
  have massLimit := (uniform_finite_quadratic_integrals_completion Vertices degrees measure placement degreeWeak values target 0 uniform).1
  have finiteInequality (depth : ℕ) : parameter * (∫ vertex, values depth vertex ^ 2 ∂degreeMeasure (endpoint depth)) ≤
      ∫ vertex, (finiteCountingClockDensityCompletion (endpoint depth) vertex - 1) * values depth vertex ∂degreeMeasure (endpoint depth) := by
    have identity := finiteGraphResolvent_energy_identity (endpoint depth) (positiveDegree depth) parameter (scale depth)
      (values depth) (fun vertex => finiteCountingClockDensityCompletion (endpoint depth) vertex - 1)
      (finiteGraphResolvent_equation (endpoint depth) (positiveDegree depth) parameter _ parameterPositive (mul_nonneg (by positivity) (scaleNonnegative depth)) _)
    rw [degreeMeasure_integral, degreeMeasure_integral]
    have nonnegative : 0 ≤ energy (endpoint depth) (values depth) := Finset.sum_nonneg fun edge member => sq_nonneg _
    have forcingSum : (∑ vertex, degreeWeight (endpoint depth) vertex *
        (finiteCountingClockDensityCompletion (endpoint depth) vertex - 1) * values depth vertex) =
        ∑ vertex, degreeWeight (endpoint depth) vertex * ((finiteCountingClockDensityCompletion (endpoint depth) vertex - 1) * values depth vertex) := by
      simp only [mul_assoc]
    rw [forcingSum] at identity
    nlinarith [mul_nonneg (scaleNonnegative depth) nonnegative]
  have limitNonpositive := le_of_tendsto_of_tendsto (massLimit.const_mul parameter) centeredIntegral
    (Eventually.of_forall finiteInequality)
  have massNonnegative : 0 ≤ ∫ point, target point ^ 2 ∂(measure : Measure Space) := integral_nonneg fun point => sq_nonneg _
  have massZero : (∫ point, target point ^ 2 ∂(measure : Measure Space)) = 0 := by nlinarith
  have squareIntegrable : Integrable (fun point => target point ^ 2) (measure : Measure Space) := by
    apply Integrable.of_bound (target.continuous.pow 2).measurable.aestronglyMeasurable (‖target‖ ^ 2)
    apply ae_of_all
    intro point
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have bounded : |target point| ≤ ‖target‖ := by simpa only [Real.norm_eq_abs] using target.norm_coe_le_norm point
    change target point ^ 2 ≤ ‖target‖ ^ 2
    nlinarith [norm_nonneg target, le_abs_self (target point), neg_le_abs (target point)]
  have squareAE := (integral_eq_zero_iff_of_nonneg (fun point => sq_nonneg (target point)) squareIntegrable).mp massZero
  have zeroAE : (fun point => target point) =ᵐ[(measure : Measure Space)] fun _ => 0 := squareAE.mono fun point zero => by
    exact sq_eq_zero_iff.mp zero
  have equality := (target.continuous.ae_eq_iff_eq (measure : Measure Space) continuous_const).mp zeroAE
  ext point
  exact congrFun equality point

end
end IGSIII34.Diffusion


