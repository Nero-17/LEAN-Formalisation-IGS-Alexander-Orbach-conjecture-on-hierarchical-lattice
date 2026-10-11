import IGSIII34.Diffusion.VariableSpeedWaitingLaw

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

theorem finiteVariableSpeedWalkSampleLaw_firstJumpPotential (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Vertex)
    (potential : Vertex → ℝ) (time : ℝ) :
    (fun sample : (ℕ → Vertex) × (ℕ → ℝ) =>
      firstJumpPotential potential time (sample.1, variableSpeedHoldingTimes (degree endpoint) sample)) =ᵐ[
        finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)]
      firstJumpPotential potential (degree endpoint initial * time) := by
  filter_upwards [finiteContinuousWalkSampleLaw_initial_vertex endpoint positiveDegree initial]
    with sample initialVertex
  unfold firstJumpPotential variableSpeedHoldingTimes
  simp only [initialVertex, div_le_iff₀ (positiveDegree initial), mul_comm time]

/-- The actual variable-speed expectation has first-order coefficient
`degree(initial) * (P - I)`, with a quadratic error controlled by the largest
finite-graph degree. -/
theorem finiteVariableSpeedWalkSampleLaw_generator_estimate
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) (constant : ℝ) (constantNonnegative : 0 ≤ constant)
    (bound : ∀ vertex, |potential vertex| ≤ constant)
    (maximumRate : ℝ) (maximumRateNonnegative : 0 ≤ maximumRate)
    (degreeBound : ∀ vertex, degree endpoint vertex ≤ maximumRate)
    (time : ℝ) (timeNonnegative : 0 ≤ time) :
    |(∫ sample, potential (holdingTimePath sample.1
        (variableSpeedHoldingTimes (degree endpoint) sample) time)
        ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) -
      (potential initial + (1 - Real.exp (-(degree endpoint initial * time))) *
        rateOneGenerator endpoint potential initial)| ≤
        2 * constant * (1 - Real.exp (-(maximumRate * time))) ^ 2 := by
  have potentialMeasurable : Measurable (fun sample : (ℕ → Vertex) × (ℕ → ℝ) =>
      potential (holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample) time)) :=
    (measurable_of_countable potential).comp ((holdingTimePath_measurable time).comp
      (measurable_fst.prodMk (variableSpeedHoldingTimes_measurable _ (measurable_of_countable _))))
  have potentialIntegrable : Integrable (fun sample : (ℕ → Vertex) × (ℕ → ℝ) =>
      potential (holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample) time))
      (finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) :=
    Integrable.of_mem_Icc (-constant) constant potentialMeasurable.aemeasurable
      (Filter.Eventually.of_forall (fun sample => abs_le.mp (bound _)))
  have firstIntegrable : Integrable (firstJumpPotential potential (degree endpoint initial * time))
      (finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) := by
    apply Integrable.of_mem_Icc (-constant) constant (firstJumpPotential_measurable potential _).aemeasurable
    filter_upwards [] with sample
    unfold firstJumpPotential
    split_ifs <;> exact abs_le.mp (bound _)
  have eventMeasurable : MeasurableSet
      {sample : (ℕ → Vertex) × (ℕ → ℝ) |
        2 ≤ holdingJumpIndex (variableSpeedHoldingTimes (degree endpoint) sample) time} :=
    measurableSet_le measurable_const ((holdingJumpIndex_measurable time).comp
      (variableSpeedHoldingTimes_measurable _ (measurable_of_countable _)))
  have normBound := norm_integral_le_of_norm_le
    ((integrable_const (2 * constant)).indicator eventMeasurable)
    (show ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial),
      ‖potential (holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample) time) -
        firstJumpPotential potential (degree endpoint initial * time) sample‖ ≤
        ({sample : (ℕ → Vertex) × (ℕ → ℝ) |
          2 ≤ holdingJumpIndex (variableSpeedHoldingTimes (degree endpoint) sample) time}).indicator
          (fun _ => 2 * constant) sample from by
      filter_upwards [finiteVariableSpeedWalkSampleLaw_regular endpoint positiveDegree (Measure.dirac initial),
        finiteVariableSpeedWalkSampleLaw_firstJumpPotential endpoint positiveDegree initial potential time]
        with sample regular firstPotential
      rw [← firstPotential]
      exact holdingTimePath_firstJump_error potential constant bound
        (sample.1, variableSpeedHoldingTimes (degree endpoint) sample) regular.1 regular.2 time timeNonnegative)
  rw [integral_sub potentialIntegrable firstIntegrable,
    firstJumpPotential_integral endpoint positiveDegree initial potential _
      (mul_nonneg (positiveDegree initial).le timeNonnegative),
    integral_indicator_const (2 * constant) eventMeasurable, smul_eq_mul, Real.norm_eq_abs] at normBound
  exact normBound.trans (by
    rw [mul_comm _ (2 * constant)]
    exact mul_le_mul_of_nonneg_left
      (finiteVariableSpeedWalkSampleLaw_two_jump_bound endpoint positiveDegree initial maximumRate
        maximumRateNonnegative degreeBound time timeNonnegative)
      (mul_nonneg (by norm_num) constantNonnegative))

end
end IGSIII34.Diffusion
