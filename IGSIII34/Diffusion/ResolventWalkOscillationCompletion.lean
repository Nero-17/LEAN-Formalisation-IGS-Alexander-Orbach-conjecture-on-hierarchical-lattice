import IGSIII34.Diffusion.WalkQuadraticVariationCompletion
import IGSIII34.Diffusion.FiniteResolventCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

theorem walkPotential_displacement_bound_completion
    (endpoint : Edge → Vertex × Vertex) (potential : Vertex → ℝ)
    (driftBound : ℝ) (generatorBound : ∀ vertex, |rateOneGenerator endpoint potential vertex| ≤ driftBound)
    (time : ℕ) (path : ℕ → Vertex) :
    |potential (path time) - potential (path 0)| ≤
      |walkCompensatedPotential endpoint potential time path| + time * driftBound := by
  have drift : |∑ index ∈ Finset.range time, rateOneGenerator endpoint potential (path index)| ≤
      time * driftBound := by
    calc
      _ ≤ ∑ index ∈ Finset.range time, |rateOneGenerator endpoint potential (path index)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _index ∈ Finset.range time, driftBound :=
        Finset.sum_le_sum fun index _ => generatorBound (path index)
      _ = _ := by simp
  calc
    _ = |walkCompensatedPotential endpoint potential time path +
        ∑ index ∈ Finset.range time, rateOneGenerator endpoint potential (path index)| := by
      congr 1
      unfold walkCompensatedPotential
      ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add le_rfl drift)

variable [Nonempty Vertex] [Nonempty Edge] [StandardBorelSpace Vertex]

/-- A proved bounded drift turns the martingale estimate into a bound on
the genuine path displacement. -/
theorem finiteDiscreteWalkLaw_stationary_oscillation_bound_completion
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (potential : Vertex → ℝ) (driftBound : ℝ) (driftNonnegative : 0 ≤ driftBound)
    (generatorBound : ∀ vertex, |rateOneGenerator endpoint potential vertex| ≤ driftBound)
    (radius : ℝ) (radiusPositive : 0 < radius) (time : ℕ)
    (shortTime : time * driftBound ≤ radius / 2) :
    ENNReal.ofReal ((radius / 2) ^ 2) *
      (finiteDiscreteWalkLaw endpoint positiveDegree (degreeMeasure endpoint))
        {path | ∃ index ≤ time, radius ≤ |potential (path index) - potential (path 0)|} ≤
      ENNReal.ofReal (time * (energy endpoint potential / Fintype.card Edge)) := by
  have inclusion : {path : ℕ → Vertex | ∃ index ≤ time,
      radius ≤ |potential (path index) - potential (path 0)|} ⊆
      {path | ∃ index ≤ time, radius / 2 ≤ |walkCompensatedPotential endpoint potential index path|} := by
    intro path witness
    obtain ⟨index, indexBound, displacement⟩ := witness
    refine ⟨index, indexBound, ?_⟩
    have deterministic := walkPotential_displacement_bound_completion endpoint potential
      driftBound generatorBound index path
    have indexReal : (index : ℝ) ≤ time := by exact_mod_cast indexBound
    have driftSmall := (mul_le_mul_of_nonneg_right indexReal driftNonnegative).trans shortTime
    linarith
  exact (mul_le_mul_left' (measure_mono inclusion) _).trans
    (finiteDiscreteWalkLaw_stationary_compensated_oscillation_bound_completion
      endpoint positiveDegree potential (radius / 2) (by positivity) time)

/-- Resolvents at the exact natural clock have bounded displacement
probability controlled only by observation time and forcing size. -/
theorem finiteGraphResolvent_stationary_oscillation_bound_completion
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter)
    (scalePositive : 0 < scale) (forcing : Vertex → ℝ)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (forcingBound : ∀ vertex, |forcing vertex| ≤ bound)
    (radius horizon : ℝ) (radiusPositive : 0 < radius) (horizonNonnegative : 0 ≤ horizon)
    (time : ℕ) (timeBound : (time : ℝ) ≤ (2 * Fintype.card Edge * scale) * horizon)
    (shortTime : 2 * bound * horizon ≤ radius / 2) :
    let potential := finiteGraphResolvent endpoint positiveDegree parameter
      (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing
    ENNReal.ofReal ((radius / 2) ^ 2) *
      (finiteDiscreteWalkLaw endpoint positiveDegree (degreeMeasure endpoint))
        {path | ∃ index ≤ time, radius ≤ |potential (path index) - potential (path 0)|} ≤
      ENNReal.ofReal (2 * horizon * (bound ^ 2 / parameter)) := by
  intro potential
  have accelerationPositive : 0 < (2 * Fintype.card Edge : ℝ) * scale := by positivity
  have generatorBound : ∀ vertex, |rateOneGenerator endpoint potential vertex| ≤
      2 * bound / (2 * Fintype.card Edge * scale) := by
    intro vertex
    have boundGenerator := finiteGraphResolvent_generator_bound endpoint positiveDegree parameter
      (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing bound forcingBound vertex
    rw [abs_mul, abs_of_pos accelerationPositive] at boundGenerator
    apply (le_div_iff₀ accelerationPositive).mpr
    nlinarith
  have driftShort : time * (2 * bound / (2 * Fintype.card Edge * scale)) ≤ radius / 2 := by
    calc
      _ ≤ ((2 * Fintype.card Edge * scale) * horizon) *
          (2 * bound / (2 * Fintype.card Edge * scale)) :=
        mul_le_mul_of_nonneg_right timeBound (by positivity)
      _ = 2 * bound * horizon := by field_simp <;> ring
      _ ≤ _ := shortTime
  have oscillation := finiteDiscreteWalkLaw_stationary_oscillation_bound_completion
    endpoint positiveDegree potential (2 * bound / (2 * Fintype.card Edge * scale))
    (by positivity) generatorBound radius radiusPositive time driftShort
  have energyNonnegative : 0 ≤ energy endpoint potential :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have energyBound := finiteGraphResolvent_scaled_energy_bound endpoint positiveDegree parameter scale
    parameterPositive scalePositive.le forcing bound boundNonnegative forcingBound
  have clockBound : time * (energy endpoint potential / Fintype.card Edge) ≤
      2 * horizon * (bound ^ 2 / parameter) := by
    calc
      _ ≤ ((2 * Fintype.card Edge * scale) * horizon) *
          (energy endpoint potential / Fintype.card Edge) :=
        mul_le_mul_of_nonneg_right timeBound (div_nonneg energyNonnegative (by positivity))
      _ = 2 * horizon * (scale * energy endpoint potential) := by field_simp <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left energyBound (by positivity)
  exact oscillation.trans (ENNReal.ofReal_le_ofReal clockBound)

end
end IGSIII34.Diffusion
