import IGSIII34.Diffusion.FiniteStoppingExitCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 4000000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [StandardBorelSpace Vertex] [Nonempty Vertex] [Nonempty Edge]

theorem finiteDiscreteWalkLaw_initial_potential_integral_completion
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) :
    (∫ path, potential (path 0) ∂finiteDiscreteWalkLaw endpoint positiveDegree (Measure.dirac initial)) =
      potential initial := by
  rw [← integral_map (measurable_pi_apply 0).aemeasurable
    (measurable_of_countable potential).aestronglyMeasurable,
    finiteDiscreteWalkLaw_initial]
  simp

/-- A resolvent approximating a local cutoff controls exit probabilities
uniformly in the starting vertex. The observation clock is the actual
full-edge clock and no stationary initial law is used. -/
theorem finiteGraphResolvent_natural_exit_bound_completion
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter)
    (scalePositive : 0 < scale) (forcing : Vertex → ℝ)
    (forcingBound : ∀ vertex, |forcing vertex| ≤ parameter)
    (initial : Vertex) (exitSet : Set Vertex)
    (initialError threshold horizon : ℝ) (thresholdBelowOne : threshold < 1)
    (horizonNonnegative : 0 ≤ horizon) (time : ℕ)
    (timeBound : (time : ℝ) ≤ (2 * Fintype.card Edge * scale) * horizon)
    (initialBound : 1 - initialError ≤ finiteGraphResolvent endpoint positiveDegree parameter
      (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing initial)
    (exitBound : ∀ vertex ∈ exitSet, finiteGraphResolvent endpoint positiveDegree parameter
      (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing vertex ≤ threshold) :
    (1 - threshold) * (finiteDiscreteWalkLaw endpoint positiveDegree (Measure.dirac initial)).real
      {path | ∃ index ≤ time, path index ∈ exitSet} ≤ initialError + 2 * parameter * horizon := by
  let potential := finiteGraphResolvent endpoint positiveDegree parameter
    (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing
  have accelerationPositive : 0 < (2 * Fintype.card Edge : ℝ) * scale := by positivity
  have potentialUpper : ∀ vertex, potential vertex ≤ 1 := by
    intro vertex
    have bound := finiteGraphResolvent_supremum_bound endpoint positiveDegree parameter
      (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing parameter forcingBound vertex
    have positiveBound : parameter / parameter = 1 := div_self parameterPositive.ne'
    rw [positiveBound] at bound
    exact (le_abs_self _).trans bound
  have generatorBound : ∀ vertex, |rateOneGenerator endpoint potential vertex| ≤
      2 * parameter / (2 * Fintype.card Edge * scale) := by
    intro vertex
    have bound := finiteGraphResolvent_generator_bound endpoint positiveDegree parameter
      (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing parameter forcingBound vertex
    rw [abs_mul, abs_of_pos accelerationPositive] at bound
    apply (le_div_iff₀ accelerationPositive).mpr
    nlinarith
  have exit := finiteDiscreteWalkLaw_exit_bound_completion endpoint positiveDegree
    (Measure.dirac initial) potential potentialUpper
    (2 * parameter / (2 * Fintype.card Edge * scale)) (by positivity)
    generatorBound threshold thresholdBelowOne time
  rw [finiteDiscreteWalkLaw_initial_potential_integral_completion] at exit
  have inclusion : {path : ℕ → Vertex | ∃ index ≤ time, path index ∈ exitSet} ⊆
      {path | ∃ index ≤ time, potential (path index) ≤ threshold} := by
    intro path witness
    obtain ⟨index, indexBound, exited⟩ := witness
    exact ⟨index, indexBound, exitBound (path index) exited⟩
  have probabilityBound := measureReal_mono
    (μ := finiteDiscreteWalkLaw endpoint positiveDegree (Measure.dirac initial)) inclusion
  have clockBound : time * (2 * parameter / (2 * Fintype.card Edge * scale)) ≤
      2 * parameter * horizon := by
    calc
      _ ≤ ((2 * Fintype.card Edge * scale) * horizon) *
          (2 * parameter / (2 * Fintype.card Edge * scale)) :=
        mul_le_mul_of_nonneg_right timeBound (by positivity)
      _ = _ := by field_simp <;> ring
  have initialDeficit : 1 - potential initial ≤ initialError := by linarith
  exact (mul_le_mul_of_nonneg_left probabilityBound (by linarith)).trans
    (exit.trans (add_le_add initialDeficit clockBound))

end
end IGSIII34.Diffusion
