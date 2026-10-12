import IGSIII34.Diffusion.TwoCoverGreedyModulusCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

variable {Vertex Edge LabelLarge LabelSmall Carrier : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [StandardBorelSpace Vertex] [Nonempty Vertex] [Fintype LabelLarge] [Fintype LabelSmall] [MetricSpace Carrier]

theorem finiteGraphResolvent_generator_unit_data_completion
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter acceleration : ℝ) (parameterPositive : 0 < parameter) (accelerationPositive : 0 < acceleration)
    (forcing : Vertex → ℝ) (forcingBound : ∀ vertex, |forcing vertex| ≤ parameter) :
    (∀ vertex, finiteGraphResolvent endpoint positiveDegree parameter acceleration parameterPositive accelerationPositive.le forcing vertex ≤ 1) ∧
      (∀ vertex, |rateOneGenerator endpoint
        (finiteGraphResolvent endpoint positiveDegree parameter acceleration parameterPositive accelerationPositive.le forcing) vertex| ≤
          2 * parameter / acceleration) := by
  refine ⟨?_, ?_⟩
  · intro vertex
    have bound := finiteGraphResolvent_supremum_bound endpoint positiveDegree parameter acceleration
      parameterPositive accelerationPositive.le forcing parameter forcingBound vertex
    rw [div_self parameterPositive.ne'] at bound
    exact (le_abs_self _).trans bound
  · intro vertex
    have bound := finiteGraphResolvent_generator_bound endpoint positiveDegree parameter acceleration
      parameterPositive accelerationPositive.le forcing parameter forcingBound vertex
    rw [abs_mul, abs_of_pos accelerationPositive] at bound
    apply (le_div_iff₀ accelerationPositive).mpr
    nlinarith

/-- Actual finite resolvents at two independently selected parameters give
the greedy path modulus bound on the supplied genuine acceleration clock.
Only finite separating covers remain to be constructed from resolvent
convergence; no potential generator estimate is left as an assumption. -/
theorem finiteGraphResolvent_two_cover_clock_modulus_completion
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (embedding : Vertex → Carrier)
    (acceleration : ℝ) (accelerationPositive : 0 < acceleration)
    (largeParameter smallParameter : ℝ) (largeParameterPositive : 0 < largeParameter) (smallParameterPositive : 0 < smallParameter)
    (largeForcing : LabelLarge → Vertex → ℝ) (smallForcing : LabelSmall → Vertex → ℝ)
    (largeForcingBound : ∀ label vertex, |largeForcing label vertex| ≤ largeParameter)
    (smallForcingBound : ∀ label vertex, |smallForcing label vertex| ≤ smallParameter)
    (radius : ℝ) (radiusPositive : 0 < radius)
    (largeError smallError largeThreshold smallThreshold : ℝ)
    (largeErrorNonnegative : 0 ≤ largeError) (smallErrorNonnegative : 0 ≤ smallError)
    (largeThresholdBelowOne : largeThreshold < 1) (smallThresholdBelowOne : smallThreshold < 1)
    (largeCover : ∀ vertex, ∃ label, 1 - largeError ≤ finiteGraphResolvent endpoint positiveDegree largeParameter acceleration
      largeParameterPositive accelerationPositive.le (largeForcing label) vertex)
    (smallCover : ∀ vertex, ∃ label, 1 - smallError ≤ finiteGraphResolvent endpoint positiveDegree smallParameter acceleration
      smallParameterPositive accelerationPositive.le (smallForcing label) vertex)
    (largeSeparating : ∀ label first last, 1 - largeError ≤ finiteGraphResolvent endpoint positiveDegree largeParameter acceleration
      largeParameterPositive accelerationPositive.le (largeForcing label) first → radius ≤ dist (embedding first) (embedding last) →
        finiteGraphResolvent endpoint positiveDegree largeParameter acceleration largeParameterPositive accelerationPositive.le (largeForcing label) last ≤ largeThreshold)
    (smallSeparating : ∀ label first last, 1 - smallError ≤ finiteGraphResolvent endpoint positiveDegree smallParameter acceleration
      smallParameterPositive accelerationPositive.le (smallForcing label) first → radius ≤ dist (embedding first) (embedding last) →
        finiteGraphResolvent endpoint positiveDegree smallParameter acceleration smallParameterPositive accelerationPositive.le (smallForcing label) last ≤ smallThreshold)
    (steps horizon largeWindow smallWindow : ℕ)
    (positiveDenominator : (horizon : ℝ) < steps * largeWindow)
    (largeDuration smallDuration : ℝ)
    (largeWindowBound : (largeWindow : ℝ) ≤ acceleration * largeDuration)
    (smallWindowBound : (smallWindow : ℝ) ≤ acceleration * smallDuration)
    (jump : ℝ) (jumpNonnegative : 0 ≤ jump)
    (jumpBound : ∀ᵐ path ∂finiteDiscreteWalkLaw endpoint positiveDegree initial,
      ∀ index < horizon, dist (embedding (path index)) (embedding (path (index + 1))) ≤ jump) :
    (finiteDiscreteWalkLaw endpoint positiveDegree initial).real
      {path | ∃ first last, first ≤ last ∧ last ≤ horizon ∧ last ≤ first + smallWindow ∧
        3 * radius + jump < dist (embedding (path first)) (embedding (path last))} ≤
      (largeWindow : ℝ) * steps *
        ((Fintype.card LabelLarge * (largeError + 2 * largeParameter * largeDuration)) / (1 - largeThreshold)) /
          ((steps : ℝ) * largeWindow - horizon) +
        steps * ((Fintype.card LabelSmall * (smallError + 2 * smallParameter * smallDuration)) / (1 - smallThreshold)) := by
  let largePotential := fun label => finiteGraphResolvent endpoint positiveDegree largeParameter acceleration largeParameterPositive accelerationPositive.le (largeForcing label)
  let smallPotential := fun label => finiteGraphResolvent endpoint positiveDegree smallParameter acceleration smallParameterPositive accelerationPositive.le (smallForcing label)
  have largeData := fun label => finiteGraphResolvent_generator_unit_data_completion endpoint positiveDegree
    largeParameter acceleration largeParameterPositive accelerationPositive (largeForcing label) (largeForcingBound label)
  have smallData := fun label => finiteGraphResolvent_generator_unit_data_completion endpoint positiveDegree
    smallParameter acceleration smallParameterPositive accelerationPositive (smallForcing label) (smallForcingBound label)
  have bound := finiteDiscreteWalkLaw_two_cover_modulus_probability_completion endpoint positiveDegree initial
    embedding largePotential (fun label => (largeData label).1) (2 * largeParameter / acceleration) (by positivity)
    (fun label => (largeData label).2) radius largeError largeThreshold radiusPositive largeErrorNonnegative
    largeThresholdBelowOne largeCover largeSeparating smallPotential (fun label => (smallData label).1)
    (2 * smallParameter / acceleration) (by positivity) (fun label => (smallData label).2)
    smallError smallThreshold smallErrorNonnegative smallThresholdBelowOne smallCover smallSeparating
    steps horizon largeWindow smallWindow positiveDenominator jump jumpNonnegative jumpBound
  have windowProduct (parameter : ℝ) (parameterPositive : 0 < parameter) (window : ℕ) (duration : ℝ)
      (windowBound : (window : ℝ) ≤ acceleration * duration) :
      window * (2 * parameter / acceleration) ≤ 2 * parameter * duration := by
    calc
      _ ≤ (acceleration * duration) * (2 * parameter / acceleration) :=
        mul_le_mul_of_nonneg_right windowBound (by positivity)
      _ = _ := by field_simp
  have largeProduct := windowProduct largeParameter largeParameterPositive largeWindow largeDuration largeWindowBound
  have smallProduct := windowProduct smallParameter smallParameterPositive smallWindow smallDuration smallWindowBound
  refine bound.trans (add_le_add ?_ ?_)
  · apply div_le_div_of_nonneg_right _ (by linarith)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left (add_le_add_right largeProduct largeError) (Nat.cast_nonneg _)
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply div_le_div_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left (add_le_add_right smallProduct smallError) (Nat.cast_nonneg _)

end
end IGSIII34.Diffusion
