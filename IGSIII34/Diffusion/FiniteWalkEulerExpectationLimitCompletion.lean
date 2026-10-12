import IGSIII34.Diffusion.FiniteWalkPairedEulerCompletion
import IGSIII34.Diffusion.EigenEulerUniformCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped _root_.Topology

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [StandardBorelSpace Vertex] [Nonempty Vertex]

/-- Bounded past tests control the actual perturbed Euler residual on the
true walk probability, uniformly in every future discrete step. -/
theorem finite_walk_paired_euler_residual_completion
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (potential error : Vertex → ℝ) (acceleration eigenvalue : ℝ) (accelerationPositive : 0 < acceleration)
    (generator : ∀ vertex, acceleration * rateOneGenerator endpoint potential vertex = -eigenvalue * potential vertex + error vertex)
    (time : ℕ) (past : (ℕ → Vertex) → ℝ)
    (pastKnown : StronglyMeasurable[Filtration.piLE time] past)
    (pastSquareIntegrable : MemLp past 2 (finiteDiscreteWalkLaw endpoint positiveDegree initial))
    (pastBound errorBound : ℝ) (pastBoundNonnegative : 0 ≤ pastBound)
    (boundedPast : ∀ path, |past path| ≤ pastBound) (boundedError : ∀ vertex, |error vertex| ≤ errorBound) :
    |(∫ path, past path * potential (path (time + 1)) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) -
      (1 - eigenvalue / acceleration) * (∫ path, past path * potential (path time) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial)| ≤
      pastBound * errorBound / acceleration := by
  let law := finiteDiscreteWalkLaw endpoint positiveDegree initial
  have residual := finite_walk_paired_euler_completion endpoint positiveDegree initial potential error acceleration eigenvalue accelerationPositive
    generator time past pastKnown pastSquareIntegrable
  rw [residual]
  simp only [add_sub_cancel_left, abs_div, abs_of_pos accelerationPositive]
  apply div_le_div_of_nonneg_right _ accelerationPositive.le
  have estimate := norm_integral_le_of_norm_le_const (μ := law) (f := fun path => past path * error (path time))
    (C := pastBound * errorBound) (Eventually.of_forall fun path => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (boundedPast path) (boundedError (path time)) (abs_nonneg _) pastBoundNonnegative)
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using estimate

/-- True full-past finite-walk paired moments converge to the exponential
spectral expectation. The generator error is required only to vanish
uniformly, exactly as provided by genuine resolvent correctors. -/
theorem finite_walk_paired_euler_tendsto_completion
    (Vertices Edges : ℕ → Type*) [∀ depth, Fintype (Vertices depth)]
    [∀ depth, DecidableEq (Vertices depth)] [∀ depth, Nonempty (Vertices depth)]
    [∀ depth, MeasurableSpace (Vertices depth)] [∀ depth, MeasurableSingletonClass (Vertices depth)]
    [∀ depth, StandardBorelSpace (Vertices depth)] [∀ depth, Fintype (Edges depth)]
    (endpoint : ∀ depth, Edges depth → Vertices depth × Vertices depth)
    (positiveDegree : ∀ depth vertex, 0 < degree (endpoint depth) vertex)
    (initial : ∀ depth, ProbabilityMeasure (Vertices depth))
    (potentials errors : ∀ depth, Vertices depth → ℝ)
    (scales : ℕ → ℝ) (scalePositive : ∀ depth, 0 < scales depth) (diverges : Tendsto scales atTop atTop)
    (eigenvalue : ℝ) (eigenvalueNonnegative : 0 ≤ eigenvalue)
    (generator : ∀ depth vertex, scales depth * rateOneGenerator (endpoint depth) (potentials depth) vertex =
      -eigenvalue * potentials depth vertex + errors depth vertex)
    (uniformError : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex, |errors depth vertex| < tolerance)
    (past : ∀ depth, (ℕ → Vertices depth) → ℝ) (start steps : ℕ → ℕ)
    (pastKnown : ∀ depth step, StronglyMeasurable[Filtration.piLE (start depth + step)] (past depth))
    (pastSquareIntegrable : ∀ depth, MemLp (past depth) 2 (finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)))
    (pastBound : ℝ) (pastBoundNonnegative : 0 ≤ pastBound) (boundedPast : ∀ depth path, |past depth path| ≤ pastBound)
    (time initialMoment : ℝ)
    (timeLimit : Tendsto (fun depth => (steps depth : ℝ) / scales depth) atTop (𝓝 time))
    (initialLimit : Tendsto (fun depth => ∫ path, past depth path * potentials depth (path (start depth))
      ∂finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)) atTop (𝓝 initialMoment)) :
    Tendsto (fun depth => ∫ path, past depth path * potentials depth (path (start depth + steps depth))
      ∂finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)) atTop
      (𝓝 (Real.exp (-eigenvalue * time) * initialMoment)) := by
  let values := fun depth step => ∫ path, past depth path * potentials depth (path (start depth + step))
    ∂finiteDiscreteWalkLaw (endpoint depth) (positiveDegree depth) (initial depth)
  apply eigenEuler_uniform_recursion_tendsto_completion scales scalePositive diverges steps time timeLimit eigenvalue eigenvalueNonnegative
    values initialMoment initialLimit
  intro tolerance positive
  have denominatorPositive : 0 < pastBound + 1 := by positivity
  filter_upwards [uniformError (tolerance / (pastBound + 1)) (by positivity)] with depth errorSmall
  intro step
  have residual := finite_walk_paired_euler_residual_completion (endpoint depth) (positiveDegree depth) (initial depth)
    (potentials depth) (errors depth) (scales depth) eigenvalue (scalePositive depth) (generator depth) (start depth + step)
    (past depth) (pastKnown depth step) (pastSquareIntegrable depth) pastBound (tolerance / (pastBound + 1))
    pastBoundNonnegative (boundedPast depth) (fun vertex => (errorSmall vertex).le)
  change |values depth (step + 1) - (1 - eigenvalue / scales depth) * values depth step| ≤ tolerance / scales depth
  have bound : pastBound * (tolerance / (pastBound + 1)) ≤ tolerance := by
    have cancellation : (pastBound + 1) * (tolerance / (pastBound + 1)) = tolerance := by field_simp
    nlinarith [div_pos positive denominatorPositive]
  exact residual.trans (div_le_div_of_nonneg_right bound (scalePositive depth).le)

end
end IGSIII34.Diffusion
