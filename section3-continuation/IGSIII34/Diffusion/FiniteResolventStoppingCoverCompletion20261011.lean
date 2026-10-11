import IGSIII34.Diffusion.FiniteCutoffExitCoverCompletion20261011
import IGSIII34.Diffusion.FiniteResolventExitCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

variable {Vertex Edge Label Carrier : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [StandardBorelSpace Vertex] [Nonempty Vertex] [Nonempty Edge] [Fintype Label] [MetricSpace Carrier]

/-- The constructed finite resolvents give an exact-clock conditional
metric escape bound, uniformly over random starting times and events known
then. The separating cover is the remaining analytic input, not a hidden
path-convergence assumption. -/
theorem finiteGraphResolvent_stopping_cover_exit_completion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (embedding : Vertex → Carrier) (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scalePositive : 0 < scale)
    (forcing : Label → Vertex → ℝ) (forcingBound : ∀ label vertex, |forcing label vertex| ≤ parameter)
    (radius error threshold : ℝ) (errorNonnegative : 0 ≤ error) (thresholdBelowOne : threshold < 1)
    (cover : ∀ vertex, ∃ label, 1 - error ≤ finiteGraphResolvent endpoint positiveDegree parameter
      (2 * Fintype.card Edge * scale) parameterPositive (by positivity) (forcing label) vertex)
    (separating : ∀ label first last, 1 - error ≤ finiteGraphResolvent endpoint positiveDegree parameter
      (2 * Fintype.card Edge * scale) parameterPositive (by positivity) (forcing label) first →
      radius ≤ dist (embedding first) (embedding last) → finiteGraphResolvent endpoint positiveDegree parameter
      (2 * Fintype.card Edge * scale) parameterPositive (by positivity) (forcing label) last ≤ threshold)
    (first : (ℕ → Vertex) → WithTop ℕ) (firstStopping : IsStoppingTime Filtration.piLE first)
    (horizon window : ℕ) (bounded : ∀ path, first path ≤ horizon)
    (duration : ℝ) (windowBound : (window : ℝ) ≤ (2 * Fintype.card Edge * scale) * duration)
    (event : Set (ℕ → Vertex)) (known : MeasurableSet[firstStopping.measurableSpace] event) :
    (1 - threshold) * (finiteDiscreteWalkLaw endpoint positiveDegree initial).real
      (event ∩ {path | ∃ index, (first path).untopA ≤ index ∧ index ≤ (first path).untopA + window ∧
        radius ≤ dist (embedding (path (first path).untopA)) (embedding (path index))}) ≤
      Fintype.card Label * (error + 2 * parameter * duration) *
        (finiteDiscreteWalkLaw endpoint positiveDegree initial).real event := by
  let potentials (label : Label) := finiteGraphResolvent endpoint positiveDegree parameter
    (2 * Fintype.card Edge * scale) parameterPositive (by positivity) (forcing label)
  have accelerationPositive : 0 < (2 * Fintype.card Edge : ℝ) * scale := by positivity
  have potentialUpper : ∀ label vertex, potentials label vertex ≤ 1 := by
    intro label vertex
    have bound := finiteGraphResolvent_supremum_bound endpoint positiveDegree parameter
      (2 * Fintype.card Edge * scale) parameterPositive (by positivity) (forcing label) parameter (forcingBound label) vertex
    rw [div_self parameterPositive.ne'] at bound
    exact (le_abs_self _).trans bound
  have generatorBound : ∀ label vertex, |rateOneGenerator endpoint (potentials label) vertex| ≤
      2 * parameter / (2 * Fintype.card Edge * scale) := by
    intro label vertex
    have bound := finiteGraphResolvent_generator_bound endpoint positiveDegree parameter
      (2 * Fintype.card Edge * scale) parameterPositive (by positivity) (forcing label) parameter (forcingBound label) vertex
    rw [abs_mul, abs_of_pos accelerationPositive] at bound
    apply (le_div_iff₀ accelerationPositive).mpr
    nlinarith
  have escape := finiteDiscreteWalkLaw_cutoff_cover_exit_completion20261011 endpoint positiveDegree initial
    embedding potentials potentialUpper (2 * parameter / (2 * Fintype.card Edge * scale)) (by positivity) generatorBound
    radius error threshold errorNonnegative thresholdBelowOne cover separating first firstStopping horizon window bounded event known
  have clockBound : window * (2 * parameter / (2 * Fintype.card Edge * scale)) ≤ 2 * parameter * duration := by
    calc
      _ ≤ ((2 * Fintype.card Edge * scale) * duration) *
        (2 * parameter / (2 * Fintype.card Edge * scale)) := mul_le_mul_of_nonneg_right windowBound (by positivity)
      _ = _ := by field_simp <;> ring
  have withError : error + window * (2 * parameter / (2 * Fintype.card Edge * scale)) ≤
      error + 2 * parameter * duration := by linarith
  exact escape.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left withError (Nat.cast_nonneg _)) (measureReal_nonneg))

end
end IGSIII34.Diffusion
