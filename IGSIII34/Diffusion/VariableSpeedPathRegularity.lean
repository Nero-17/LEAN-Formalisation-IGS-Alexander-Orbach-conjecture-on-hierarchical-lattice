import IGSIII34.Diffusion.VariableSpeedWalkConstruction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

theorem finiteVariableSpeedWalkSampleLaw_locally_constant_right
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) :
    ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree initial,
      ∀ time : ℝ, 0 ≤ time → ∃ intervalLength : ℝ, 0 < intervalLength ∧
        ∀ nextTime : ℝ, time ≤ nextTime → nextTime < time + intervalLength →
          holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample) nextTime =
            holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample) time := by
  filter_upwards [finiteVariableSpeedWalkSampleLaw_regular endpoint positiveDegree initial] with sample regular
  exact holdingTimePath_locally_constant_right _ _ regular.1 regular.2

theorem finiteVariableSpeedWalkSampleLaw_locally_constant_left
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) :
    ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree initial,
      ∀ time : ℝ, 0 < time → ∃ intervalLength : ℝ, 0 < intervalLength ∧ ∃ leftValue : Vertex,
        ∀ previousTime : ℝ, time - intervalLength < previousTime → previousTime < time →
          holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample) previousTime = leftValue := by
  filter_upwards [finiteVariableSpeedWalkSampleLaw_regular endpoint positiveDegree initial] with sample regular
  exact holdingTimePath_locally_constant_left _ _ regular.1 regular.2

theorem finiteVariableSpeedWalkSampleLaw_right_continuous [TopologicalSpace Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) :
    ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree initial,
      ∀ time : ℝ, 0 ≤ time → ContinuousWithinAt
        (holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample)) (Set.Ici time) time := by
  filter_upwards [finiteVariableSpeedWalkSampleLaw_locally_constant_right endpoint positiveDegree initial] with sample constant
  intro time timeNonnegative
  obtain ⟨intervalLength, intervalPositive, equality⟩ := constant time timeNonnegative
  apply tendsto_const_nhds.congr'
  filter_upwards [Ico_mem_nhdsGE (lt_add_of_pos_right time intervalPositive)] with nextTime bounds
  exact (equality nextTime bounds.1 bounds.2).symm

theorem finiteVariableSpeedWalkSampleLaw_left_limit [TopologicalSpace Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) :
    ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree initial,
      ∀ time : ℝ, 0 < time → ∃ leftValue : Vertex,
        Tendsto (holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample))
          (𝓝[Set.Iio time] time) (𝓝 leftValue) := by
  filter_upwards [finiteVariableSpeedWalkSampleLaw_locally_constant_left endpoint positiveDegree initial] with sample constant
  intro time timePositive
  obtain ⟨intervalLength, intervalPositive, leftValue, equality⟩ := constant time timePositive
  refine ⟨leftValue, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsLT (sub_lt_self time intervalPositive)] with previousTime bounds
  exact (equality previousTime bounds.1 bounds.2).symm

end
end IGSIII34.Diffusion
