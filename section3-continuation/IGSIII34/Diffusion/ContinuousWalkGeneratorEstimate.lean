import IGSIII34.Diffusion.ContinuousWalkFirstOrder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

theorem holdingTimePath_firstJump_error (potential : Vertex → ℝ)
    (constant : ℝ) (bound : ∀ vertex, |potential vertex| ≤ constant)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) (positive : ∀ index, 0 < sample.2 index)
    (nonexplosion : Tendsto (cumulativeHoldingTime sample.2) atTop atTop)
    (time : ℝ) (timeNonnegative : 0 ≤ time) :
    |potential (holdingTimePath sample.1 sample.2 time) - firstJumpPotential potential time sample| ≤
      ({sample : (ℕ → Vertex) × (ℕ → ℝ) | 2 ≤ holdingJumpIndex sample.2 time}).indicator
        (fun _ => 2 * constant) sample := by
  have zeroIndex := holdingJumpIndex_eq_zero_iff sample.2 positive nonexplosion time timeNonnegative
  by_cases two : 2 ≤ holdingJumpIndex sample.2 time
  · have jumped : sample.2 0 ≤ time := by
      by_contra failure
      have indexZero := zeroIndex.mpr (lt_of_not_ge failure)
      omega
    simp only [Set.indicator, Set.mem_setOf_eq, two, if_true, firstJumpPotential, jumped]
    exact (abs_sub _ _).trans (by linarith [bound (holdingTimePath sample.1 sample.2 time), bound (sample.1 1)])
  · have count : holdingJumpIndex sample.2 time = 0 ∨ holdingJumpIndex sample.2 time = 1 := by omega
    rcases count with count | count
    · have noJump := zeroIndex.mp count
      simp [Set.indicator, two, firstJumpPotential, not_le.mpr noJump, holdingTimePath, count]
    · have jumped : sample.2 0 ≤ time := by
        by_contra failure
        have indexZero := zeroIndex.mpr (lt_of_not_ge failure)
        omega
      simp [Set.indicator, two, firstJumpPotential, jumped, holdingTimePath, count]

theorem finiteContinuousWalkSampleLaw_two_jump_bound (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex)
    [IsProbabilityMeasure initial] (time : ℝ) (timeNonnegative : 0 ≤ time) :
    (finiteContinuousWalkSampleLaw endpoint positiveDegree initial).real
      {sample | 2 ≤ holdingJumpIndex sample.2 time} ≤ (1 - Real.exp (-time)) ^ 2 := by
  have measurable : MeasurableSet {holdingTimes : ℕ → ℝ | 2 ≤ holdingJumpIndex holdingTimes time} :=
    measurableSet_le measurable_const (holdingJumpIndex_measurable time)
  have mapped := congrArg (fun measure : Measure (ℕ → ℝ) =>
      measure.real {holdingTimes | 2 ≤ holdingJumpIndex holdingTimes time})
    (finiteContinuousWalkSampleLaw_holdingTimes endpoint positiveDegree initial)
  rw [map_measureReal_apply measurable_snd measurable] at mapped
  exact mapped.trans_le (exponentialHoldingTimeLaw_two_jump_bound time timeNonnegative)

/-- A quadratic error estimate for the true continuous-time walk expectation,
with the actual graph generator and an explicit constant. No Markov or
limiting-process existence theorem is an input. -/
theorem finiteContinuousWalkSampleLaw_generator_estimate
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) (constant : ℝ) (constantNonnegative : 0 ≤ constant)
    (bound : ∀ vertex, |potential vertex| ≤ constant) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    |(∫ sample, potential (holdingTimePath sample.1 sample.2 time)
        ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) -
      (potential initial + (1 - Real.exp (-time)) * rateOneGenerator endpoint potential initial)| ≤
        2 * constant * (1 - Real.exp (-time)) ^ 2 := by
  have potentialMeasurable : Measurable (fun sample : (ℕ → Vertex) × (ℕ → ℝ) =>
      potential (holdingTimePath sample.1 sample.2 time)) :=
    (measurable_of_countable potential).comp (holdingTimePath_measurable time)
  have potentialIntegrable : Integrable (fun sample : (ℕ → Vertex) × (ℕ → ℝ) =>
      potential (holdingTimePath sample.1 sample.2 time))
      (finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) :=
    Integrable.of_mem_Icc (-constant) constant potentialMeasurable.aemeasurable
      (Filter.Eventually.of_forall (fun sample => abs_le.mp (bound _)))
  have firstIntegrable : Integrable (firstJumpPotential potential time)
      (finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) := by
    apply Integrable.of_mem_Icc (-constant) constant (firstJumpPotential_measurable potential time).aemeasurable
    filter_upwards [] with sample
    unfold firstJumpPotential
    split_ifs <;> exact abs_le.mp (bound _)
  have eventMeasurable : MeasurableSet
      {sample : (ℕ → Vertex) × (ℕ → ℝ) | 2 ≤ holdingJumpIndex sample.2 time} :=
    measurableSet_le measurable_const ((holdingJumpIndex_measurable time).comp measurable_snd)
  have normBound := norm_integral_le_of_norm_le
    ((integrable_const (2 * constant)).indicator eventMeasurable)
    (show ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial),
      ‖potential (holdingTimePath sample.1 sample.2 time) - firstJumpPotential potential time sample‖ ≤
        ({sample : (ℕ → Vertex) × (ℕ → ℝ) | 2 ≤ holdingJumpIndex sample.2 time}).indicator
          (fun _ => 2 * constant) sample from by
      filter_upwards [finiteContinuousWalkSampleLaw_regular endpoint positiveDegree (Measure.dirac initial)]
        with sample regular
      exact holdingTimePath_firstJump_error potential constant bound sample regular.1 regular.2.1 time timeNonnegative)
  rw [integral_sub potentialIntegrable firstIntegrable,
    firstJumpPotential_integral endpoint positiveDegree initial potential time timeNonnegative,
    integral_indicator_const (2 * constant) eventMeasurable, smul_eq_mul, Real.norm_eq_abs] at normBound
  exact normBound.trans (by
    rw [mul_comm _ (2 * constant)]
    exact mul_le_mul_of_nonneg_left
      (finiteContinuousWalkSampleLaw_two_jump_bound endpoint positiveDegree (Measure.dirac initial) time timeNonnegative)
      (mul_nonneg (by norm_num) constantNonnegative))

end
end IGSIII34.Diffusion
