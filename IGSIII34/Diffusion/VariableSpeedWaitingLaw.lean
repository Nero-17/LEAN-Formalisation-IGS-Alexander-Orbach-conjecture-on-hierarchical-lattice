import IGSIII34.Diffusion.VariableSpeedWalkConstruction
import IGSIII34.Diffusion.ContinuousWalkGeneratorEstimate

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

theorem finiteContinuousWalkSampleLaw_initial_vertex (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Vertex) :
    ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial),
      sample.1 0 = initial := by
  have mapped : ∀ᵐ vertex ∂(finiteDiscreteWalkLaw endpoint positiveDegree (Measure.dirac initial)).map
      (fun path => path 0), vertex = initial := by
    rw [finiteDiscreteWalkLaw_initial]
    simp
  have discrete := ae_of_ae_map (measurable_pi_apply 0).aemeasurable mapped
  exact quasiMeasurePreserving_fst.ae discrete

/-- The first waiting time of the actual variable-speed path is exponential
with rate equal to the starting vertex degree. -/
theorem finiteVariableSpeedWalkSampleLaw_no_jump (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Vertex)
    (time : ℝ) (timeNonnegative : 0 ≤ time) :
    (finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)).real
      {sample | holdingJumpIndex (variableSpeedHoldingTimes (degree endpoint) sample) time = 0} =
        Real.exp (-(degree endpoint initial * time)) := by
  have equality :
      {sample : (ℕ → Vertex) × (ℕ → ℝ) |
        holdingJumpIndex (variableSpeedHoldingTimes (degree endpoint) sample) time = 0} =ᵐ[
          finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)]
      {sample | degree endpoint initial * time < sample.2 0} := by
    filter_upwards [finiteVariableSpeedWalkSampleLaw_regular endpoint positiveDegree (Measure.dirac initial),
      finiteContinuousWalkSampleLaw_initial_vertex endpoint positiveDegree initial] with sample regular initialVertex
    apply propext
    change holdingJumpIndex (variableSpeedHoldingTimes (degree endpoint) sample) time = 0 ↔
      degree endpoint initial * time < sample.2 0
    rw [holdingJumpIndex_eq_zero_iff _ regular.1 regular.2 time timeNonnegative]
    unfold variableSpeedHoldingTimes
    rw [initialVertex, lt_div_iff₀ (positiveDegree initial), mul_comm time]
  rw [measureReal_congr equality]
  have mapped := congrArg (fun measure : Measure (ℕ → ℝ) =>
      measure.real {holdingTimes | degree endpoint initial * time < holdingTimes 0})
    (finiteContinuousWalkSampleLaw_holdingTimes endpoint positiveDegree (Measure.dirac initial))
  rw [map_measureReal_apply measurable_snd
    (measurableSet_lt measurable_const (measurable_pi_apply 0))] at mapped
  exact mapped.trans (exponentialHoldingTimeLaw_survival 0 _ (mul_nonneg (positiveDegree initial).le timeNonnegative))

theorem exponentialHoldingTimeLaw_two_coordinate_cdf (time : ℝ) (timeNonnegative : 0 ≤ time) :
    exponentialHoldingTimeLaw.real {holdingTimes | holdingTimes 0 ≤ time ∧ holdingTimes 1 ≤ time} =
      (1 - Real.exp (-time)) ^ 2 := by
  have intersection := (exponentialHoldingTimeLaw_independent.indepFun (i := 0) (j := 1) (by decide)).measure_inter_preimage_eq_mul
    (Set.Iic time) (Set.Iic time) measurableSet_Iic measurableSet_Iic
  change (exponentialHoldingTimeLaw
    ((fun holdingTimes : ℕ → ℝ => holdingTimes 0) ⁻¹' Set.Iic time ∩
      (fun holdingTimes : ℕ → ℝ => holdingTimes 1) ⁻¹' Set.Iic time)).toReal = _
  rw [intersection, ENNReal.toReal_mul]
  change exponentialHoldingTimeLaw.real {holdingTimes | holdingTimes 0 ≤ time} *
    exponentialHoldingTimeLaw.real {holdingTimes | holdingTimes 1 ≤ time} = _
  rw [exponentialHoldingTimeLaw_coordinate_cdf 0 time timeNonnegative,
    exponentialHoldingTimeLaw_coordinate_cdf 1 time timeNonnegative, pow_two]

theorem finiteVariableSpeedWalkSampleLaw_two_jump_bound (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Vertex)
    (maximumRate : ℝ) (maximumRateNonnegative : 0 ≤ maximumRate)
    (degreeBound : ∀ vertex, degree endpoint vertex ≤ maximumRate)
    (time : ℝ) (timeNonnegative : 0 ≤ time) :
    (finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)).real
      {sample | 2 ≤ holdingJumpIndex (variableSpeedHoldingTimes (degree endpoint) sample) time} ≤
        (1 - Real.exp (-(maximumRate * time))) ^ 2 := by
  have inclusion :
      {sample : (ℕ → Vertex) × (ℕ → ℝ) |
        2 ≤ holdingJumpIndex (variableSpeedHoldingTimes (degree endpoint) sample) time} ≤ᵐ[
          finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)]
      {sample | sample.2 0 ≤ maximumRate * time ∧ sample.2 1 ≤ maximumRate * time} := by
    filter_upwards [finiteVariableSpeedWalkSampleLaw_regular endpoint positiveDegree (Measure.dirac initial)]
      with sample regular
    intro jumps
    have sumBound := (holdingJumpIndex_ge_iff _ regular.1 regular.2 time timeNonnegative 2).mp jumps
    simp only [cumulativeHoldingTime, Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at sumBound
    have firstBound : variableSpeedHoldingTimes (degree endpoint) sample 0 ≤ time := by linarith [regular.1 1]
    have nextBound : variableSpeedHoldingTimes (degree endpoint) sample 1 ≤ time := by linarith [regular.1 0]
    unfold variableSpeedHoldingTimes at firstBound nextBound
    constructor
    · exact ((div_le_iff₀ (positiveDegree _)).mp firstBound).trans
        (by nlinarith [degreeBound (sample.1 0)])
    · exact ((div_le_iff₀ (positiveDegree _)).mp nextBound).trans
        (by nlinarith [degreeBound (sample.1 1)])
  have mapped := congrArg (fun measure : Measure (ℕ → ℝ) =>
      measure.real {holdingTimes | holdingTimes 0 ≤ maximumRate * time ∧ holdingTimes 1 ≤ maximumRate * time})
    (finiteContinuousWalkSampleLaw_holdingTimes endpoint positiveDegree (Measure.dirac initial))
  have eventMeasurable : MeasurableSet {holdingTimes : ℕ → ℝ |
      holdingTimes 0 ≤ maximumRate * time ∧ holdingTimes 1 ≤ maximumRate * time} :=
    (measurableSet_le (measurable_pi_apply 0) measurable_const).inter
      (measurableSet_le (measurable_pi_apply 1) measurable_const)
  rw [map_measureReal_apply measurable_snd eventMeasurable] at mapped
  exact (ENNReal.toReal_mono (by finiteness) (measure_mono_ae inclusion)).trans
    (mapped.trans (exponentialHoldingTimeLaw_two_coordinate_cdf _ (mul_nonneg maximumRateNonnegative timeNonnegative))).le

end
end IGSIII34.Diffusion
