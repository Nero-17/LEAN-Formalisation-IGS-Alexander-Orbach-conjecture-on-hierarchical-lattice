import IGSIII34.Diffusion.FiniteWeightedHoldingPathsCompletion

set_option autoImplicit false
set_option maxHeartbeats 3200000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators _root_.Topology

theorem cumulativeHoldingTime_const_mul_completion
    (holding : ℕ → ℝ) (scalar : ℝ) (count : ℕ) :
    cumulativeHoldingTime (fun index => scalar * holding index) count = scalar * cumulativeHoldingTime holding count := by
  simp only [cumulativeHoldingTime, Finset.mul_sum]

theorem holdingJumpIndex_const_mul_completion
    (holding : ℕ → ℝ) (positive : ∀ index, 0 < holding index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holding) atTop atTop)
    (scalar : ℝ) (scalarPositive : 0 < scalar) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    holdingJumpIndex (fun index => scalar * holding index) (scalar * time) = holdingJumpIndex holding time := by
  have interval := holdingJumpIndex_interval holding (fun index => (positive index).le) nonexplosion time timeNonnegative
  apply holdingJumpIndex_eq_of_interval _ (fun index => (mul_pos scalarPositive (positive index)).le)
  · rw [cumulativeHoldingTime_const_mul_completion]
    exact mul_le_mul_of_nonneg_left interval.1 scalarPositive.le
  · rw [cumulativeHoldingTime_const_mul_completion]
    exact mul_lt_mul_of_pos_left interval.2 scalarPositive

theorem holdingTimePath_const_mul_completion
    {Vertex : Type*} (trajectory : ℕ → Vertex) (holding : ℕ → ℝ) (positive : ∀ index, 0 < holding index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holding) atTop atTop)
    (scalar : ℝ) (scalarPositive : 0 < scalar) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    holdingTimePath trajectory (fun index => scalar * holding index) (scalar * time) = holdingTimePath trajectory holding time := by
  unfold holdingTimePath
  rw [holdingJumpIndex_const_mul_completion holding positive nonexplosion scalar scalarPositive time timeNonnegative]

variable {Vertex Edge : Type*} [Fintype Vertex] [Nonempty Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge] [Nonempty Edge]

/-- The q-weighted degree clock is exactly the vertex-variable-speed clock:
the actual holding time is Exp(1)/degree and the acceleration is |V| scale. -/
theorem finiteCountingClockDensity_vertex_clock_identity_completion
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (scale : ℝ) (scalePositive : 0 < scale) :
    ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex), ∀ time : ℝ, 0 ≤ time →
      holdingTimePath sample.1 (weightedHoldingSampleCompletion (finiteCountingClockDensityCompletion endpoint) sample).2
        ((2 * Fintype.card Edge : ℝ) * scale * time) =
      holdingTimePath sample.1 (fun index => sample.2 index / degree endpoint (sample.1 index))
        ((Fintype.card Vertex : ℝ) * scale * time) := by
  have original : ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex),
      (∀ index, 0 < sample.2 index) ∧ Tendsto (cumulativeHoldingTime sample.2) atTop atTop :=
    (finiteContinuousWalkSampleLaw_regular endpoint positiveDegree (initial : Measure Vertex)).mono
    (fun _ clock => ⟨clock.1, clock.2.1⟩)
  have inverseDegreePositive : ∀ vertex, 0 < (degree endpoint vertex)⁻¹ := fun vertex => inv_pos.mpr (positiveDegree vertex)
  have weighted := weightedHoldingSample_regular_completion
    (finiteContinuousWalkSampleLaw endpoint positiveDegree (initial : Measure Vertex))
    (fun vertex => (degree endpoint vertex)⁻¹) inverseDegreePositive original
  filter_upwards [weighted] with sample clock
  intro time timeNonnegative
  let holding := fun index => sample.2 index / degree endpoint (sample.1 index)
  have holdingPositive : ∀ index, 0 < holding index := by
    intro index
    simpa only [holding, weightedHoldingSampleCompletion, div_eq_mul_inv, mul_comm] using clock.1 index
  have holdingNonexplosion : Tendsto (cumulativeHoldingTime holding) atTop atTop := by
    simpa only [holding, weightedHoldingSampleCompletion, div_eq_mul_inv, mul_comm] using clock.2
  let scalar : ℝ := (2 * Fintype.card Edge) / (Fintype.card Vertex : ℝ)
  have scalarPositive : 0 < scalar := by dsimp [scalar]; positivity
  have holdingIdentity : (weightedHoldingSampleCompletion (finiteCountingClockDensityCompletion endpoint) sample).2 =
      fun index => scalar * holding index := by
    funext index
    dsimp only [weightedHoldingSampleCompletion, finiteCountingClockDensityCompletion, scalar, holding]
    field_simp
  have scaleIdentity : (2 * Fintype.card Edge : ℝ) * scale * time = scalar * ((Fintype.card Vertex : ℝ) * scale * time) := by
    dsimp only [scalar]
    field_simp
  rw [holdingIdentity, scaleIdentity]
  exact holdingTimePath_const_mul_completion sample.1 holding holdingPositive holdingNonexplosion scalar scalarPositive
    ((Fintype.card Vertex : ℝ) * scale * time) (mul_nonneg (mul_pos (by positivity) scalePositive).le timeNonnegative)

end
end IGSIII34.Diffusion
