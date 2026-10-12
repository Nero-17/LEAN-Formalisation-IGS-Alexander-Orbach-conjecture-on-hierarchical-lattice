import IGSIII34.Diffusion.HoldingTimePaths
import IGSIII34.Diffusion.DiscreteGlobalSkorokhodSampleCompletion

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal
variable {Space Vertex : Type*} [TopologicalSpace Space]

def SkorokhodCadlagCompletion (path : ℝ≥0 → Space) : Prop :=
  (∀ time, ContinuousWithinAt path (Set.Ici time) time) ∧
    ∀ time : ℝ≥0, 0 < time → ∃ value, Tendsto path (𝓝[Set.Iio time] time) (𝓝 value)

theorem continuous_path_cadlag_completion
    (path : ℝ≥0 → Space) (continuous : Continuous path) : SkorokhodCadlagCompletion path := by
  exact ⟨fun time => continuous.continuousWithinAt,
    fun time _ => ⟨path time, (continuous.tendsto time).mono_left nhdsWithin_le_nhds⟩⟩

/-- True nonexplosive holding-time samples are right continuous and have
left limits. This proves support on actual cadlag paths independently of
the topology placed on the ambient raw-function carrier. -/
theorem holdingTimePath_cadlag_completion
    (placement : Vertex → Space) (trajectory : ℕ → Vertex) (holdingTimes : ℕ → ℝ)
    (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (scale : ℝ) (scalePositive : 0 < scale) :
    SkorokhodCadlagCompletion
      (fun time : ℝ≥0 => placement (holdingTimePath trajectory holdingTimes (scale * (time : ℝ)))) := by
  constructor
  · intro time
    obtain ⟨length, lengthPositive, constant⟩ := holdingTimePath_locally_constant_right trajectory holdingTimes positive
      nonexplosion (scale * (time : ℝ)) (mul_nonneg scalePositive.le time.property)
    have upperNeighbourhood : ∀ᶠ next : ℝ≥0 in 𝓝 time, (next : ℝ) < (time : ℝ) + length / scale :=
      (NNReal.continuous_coe.tendsto time).eventually (Iio_mem_nhds (lt_add_of_pos_right (time : ℝ) (div_pos lengthPositive scalePositive)))
    change Tendsto _ (𝓝[Set.Ici time] time) _
    apply tendsto_const_nhds.congr'
    filter_upwards [upperNeighbourhood.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with next upper lower
    have equality := constant (scale * (next : ℝ))
      (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr lower) scalePositive.le) (by
        have bound := (lt_div_iff₀ scalePositive).mp (show (next : ℝ) - time < length / scale by linarith)
        nlinarith)
    exact (congrArg placement equality).symm
  · intro time timePositive
    obtain ⟨length, lengthPositive, leftValue, constant⟩ := holdingTimePath_locally_constant_left trajectory holdingTimes positive
      nonexplosion (scale * (time : ℝ)) (mul_pos scalePositive (NNReal.coe_pos.mpr timePositive))
    refine ⟨placement leftValue, ?_⟩
    have lowerNeighbourhood : ∀ᶠ previous : ℝ≥0 in 𝓝 time, (time : ℝ) - length / scale < (previous : ℝ) :=
      (NNReal.continuous_coe.tendsto time).eventually (Ioi_mem_nhds (sub_lt_self (time : ℝ) (div_pos lengthPositive scalePositive)))
    apply tendsto_const_nhds.congr'
    filter_upwards [lowerNeighbourhood.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with previous lower upper
    have equality := constant (scale * (previous : ℝ)) (by
        have bound := (lt_div_iff₀ scalePositive).mp (show (time : ℝ) - previous < length / scale by linarith)
        nlinarith)
      (mul_lt_mul_of_pos_left (NNReal.coe_lt_coe.mpr upper) scalePositive)
    exact (congrArg placement equality).symm

theorem fixedClockPath_cadlag_completion
    (placement : Vertex → Space) (trajectory : ℕ → Vertex) (scale : ℝ) (scalePositive : 0 < scale) :
    SkorokhodCadlagCompletion (fun time : ℝ≥0 => placement (trajectory ⌊scale * (time : ℝ)⌋₊)) := by
  have cumulative (count : ℕ) : cumulativeHoldingTime (fun _ => (1 : ℝ)) count = count := by
    simp [cumulativeHoldingTime]
  have nonexplosion : Tendsto (cumulativeHoldingTime (fun _ => (1 : ℝ))) atTop atTop := by
    convert tendsto_natCast_atTop_atTop (R := ℝ) using 1
    funext count
    exact cumulative count
  have identity : (fun time : ℝ≥0 => placement (holdingTimePath trajectory (fun _ => (1 : ℝ)) (scale * (time : ℝ)))) =
      (fun time : ℝ≥0 => placement (trajectory ⌊scale * (time : ℝ)⌋₊)) := by
    funext time
    unfold holdingTimePath
    rw [holdingJumpIndex_eq_of_interval (fun _ => (1 : ℝ)) (by intro index; norm_num)
      (scale * (time : ℝ)) ⌊scale * (time : ℝ)⌋₊]
    · rw [cumulative]
      exact Nat.floor_le (mul_nonneg scalePositive.le time.property)
    · rw [cumulative, Nat.cast_add, Nat.cast_one]
      exact Nat.lt_floor_add_one _
  rw [← identity]
  exact holdingTimePath_cadlag_completion placement trajectory (fun _ => (1 : ℝ))
    (by intro index; norm_num) nonexplosion scale scalePositive

end
end IGSIII34.Diffusion
