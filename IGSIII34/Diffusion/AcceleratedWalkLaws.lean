import IGSIII34.Diffusion.VariableSpeedWalkGenerator
import IGSIII34.Diffusion.VariableSpeedPathRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

def acceleratedPath {Vertex : Type*} (acceleration : ℝ≥0) (path : ℝ≥0 → Vertex)
    (time : ℝ≥0) : Vertex := path (acceleration * time)

theorem acceleratedPath_measurable {Vertex : Type*} [MeasurableSpace Vertex] (acceleration : ℝ≥0) :
    Measurable (acceleratedPath (Vertex := Vertex) acceleration) := by
  apply measurable_pi_lambda
  intro time
  exact measurable_pi_apply (acceleration * time)

theorem acceleratedPathLaw_initial {Vertex : Type*} [MeasurableSpace Vertex]
    (law : Measure (ℝ≥0 → Vertex)) (acceleration : ℝ≥0) :
    (law.map (acceleratedPath acceleration)).map (fun path => path 0) = law.map (fun path => path 0) := by
  rw [Measure.map_map (measurable_pi_apply 0) (acceleratedPath_measurable acceleration)]
  congr 1
  funext path
  simp [acceleratedPath]

theorem initial_generator_time_scale (expectation : ℝ → ℝ) (initialValue generator acceleration : ℝ)
    (accelerationPositive : 0 < acceleration)
    (generatorLimit : Tendsto (fun time : ℝ => (expectation time - initialValue) / time)
      (𝓝[>] 0) (𝓝 generator)) :
    Tendsto (fun time : ℝ => (expectation (acceleration * time) - initialValue) / time)
      (𝓝[>] 0) (𝓝 (acceleration * generator)) := by
  have scaledTime : Tendsto (fun time : ℝ => acceleration * time) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using ((show ContinuousAt (fun time : ℝ => acceleration * time) 0 by fun_prop).tendsto.mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with time timePositive
      exact mul_pos accelerationPositive timePositive
  have scaled := (generatorLimit.comp scaledTime).mul_const acceleration
  convert scaled using 1
  · funext time
    dsimp only [Function.comp_apply]
    simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
    simp [accelerationPositive.ne']
  · ring

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

def acceleratedFiniteContinuousWalkLaw (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex)
    (acceleration : ℝ≥0) : Measure (ℝ≥0 → Vertex) :=
  (finiteContinuousWalkLaw endpoint positiveDegree initial).map (acceleratedPath acceleration)

def acceleratedFiniteVariableSpeedWalkLaw (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex)
    (acceleration : ℝ≥0) : Measure (ℝ≥0 → Vertex) :=
  (finiteVariableSpeedWalkLaw endpoint positiveDegree initial).map (acceleratedPath acceleration)

instance acceleratedFiniteContinuousWalkLaw_probability (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex)
    [IsProbabilityMeasure initial] (acceleration : ℝ≥0) :
    IsProbabilityMeasure (acceleratedFiniteContinuousWalkLaw endpoint positiveDegree initial acceleration) := by
  exact isProbabilityMeasure_map (acceleratedPath_measurable acceleration).aemeasurable

instance acceleratedFiniteVariableSpeedWalkLaw_probability (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex)
    [IsProbabilityMeasure initial] (acceleration : ℝ≥0) :
    IsProbabilityMeasure (acceleratedFiniteVariableSpeedWalkLaw endpoint positiveDegree initial acceleration) := by
  exact isProbabilityMeasure_map (acceleratedPath_measurable acceleration).aemeasurable

theorem acceleratedFiniteContinuousWalkLaw_initial (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) (acceleration : ℝ≥0) :
    (acceleratedFiniteContinuousWalkLaw endpoint positiveDegree initial acceleration).map (fun path => path 0) = initial := by
  rw [acceleratedFiniteContinuousWalkLaw, acceleratedPathLaw_initial, finiteContinuousWalkLaw_initial]

theorem acceleratedFiniteVariableSpeedWalkLaw_initial (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) (acceleration : ℝ≥0) :
    (acceleratedFiniteVariableSpeedWalkLaw endpoint positiveDegree initial acceleration).map (fun path => path 0) = initial := by
  rw [acceleratedFiniteVariableSpeedWalkLaw, acceleratedPathLaw_initial, finiteVariableSpeedWalkLaw_initial]

theorem acceleratedFiniteContinuousWalkSampleLaw_generator [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) (acceleration : ℝ) (accelerationPositive : 0 < acceleration) :
    Tendsto (fun time : ℝ =>
      ((∫ sample, potential (holdingTimePath sample.1 sample.2 (acceleration * time))
          ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) - potential initial) / time)
      (𝓝[>] 0) (𝓝 (acceleration * rateOneGenerator endpoint potential initial)) :=
  initial_generator_time_scale _ _ _ acceleration accelerationPositive
    (finiteContinuousWalkSampleLaw_generator endpoint positiveDegree initial potential)

theorem acceleratedFiniteVariableSpeedWalkSampleLaw_generator [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) (acceleration : ℝ) (accelerationPositive : 0 < acceleration) :
    Tendsto (fun time : ℝ =>
      ((∫ sample, potential (holdingTimePath sample.1
          (variableSpeedHoldingTimes (degree endpoint) sample) (acceleration * time))
          ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) - potential initial) / time)
      (𝓝[>] 0) (𝓝 (acceleration * laplacian endpoint potential initial)) :=
  initial_generator_time_scale _ _ _ acceleration accelerationPositive
    (finiteVariableSpeedWalkSampleLaw_generator endpoint positiveDegree initial potential)

end
end IGSIII34.Diffusion
