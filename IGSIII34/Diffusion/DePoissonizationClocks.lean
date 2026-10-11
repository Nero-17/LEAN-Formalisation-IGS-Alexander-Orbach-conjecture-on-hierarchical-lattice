import IGSIII34.Diffusion.UniformInverseHoldingClocks

set_option autoImplicit false
set_option maxHeartbeats 1800000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter
open scoped BigOperators Topology

def dePoissonizationClock (holdingTimes : ℕ → ℝ) (acceleration time : ℝ) : ℝ :=
  cumulativeHoldingTime holdingTimes ⌊acceleration * time⌋₊ / acceleration

/-- Exact samplewise identification of the accelerated discrete walk with
the accelerated continuous walk at the exponential reparametrisation clock. -/
theorem holdingTimePath_dePoissonization {Vertex : Type*} (trajectory : ℕ → Vertex)
    (holdingTimes : ℕ → ℝ) (positive : ∀ index, 0 < holdingTimes index)
    (acceleration time : ℝ) (accelerationNonzero : acceleration ≠ 0) :
    holdingTimePath trajectory holdingTimes
      (acceleration * dePoissonizationClock holdingTimes acceleration time) =
        trajectory ⌊acceleration * time⌋₊ := by
  have clockEquality : acceleration * dePoissonizationClock holdingTimes acceleration time =
      cumulativeHoldingTime holdingTimes ⌊acceleration * time⌋₊ := by
    unfold dePoissonizationClock
    field_simp
  rw [clockEquality]
  unfold holdingTimePath
  congr 1
  apply holdingJumpIndex_eq_of_interval holdingTimes (fun index => (positive index).le)
  · exact le_rfl
  · simp only [cumulativeHoldingTime, Finset.sum_range_succ]
    exact lt_add_of_pos_right _ (positive _)

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

/-- One probability-one event supplies the exact path identity and both
uniform clock limits for every diverging positive acceleration, including
the natural finite-volume clocks once their divergence is established.
This is a clock theorem; weak convergence to a limiting diffusion is separate. -/
theorem finiteContinuousWalkSampleLaw_dePoissonization
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) :
    ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree initial,
      (∀ (acceleration time : ℝ), acceleration ≠ 0 →
        holdingTimePath sample.1 sample.2
          (acceleration * dePoissonizationClock sample.2 acceleration time) =
            sample.1 ⌊acceleration * time⌋₊) ∧
      ∀ (acceleration : ℕ → ℝ), (∀ depth, 0 < acceleration depth) →
        Tendsto acceleration atTop atTop → ∀ horizon : ℝ, 0 ≤ horizon →
          ∀ tolerance : ℝ, 0 < tolerance →
            (∀ᶠ depth in atTop, ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
              |dePoissonizationClock sample.2 (acceleration depth) time - time| < tolerance) ∧
            (∀ᶠ depth in atTop, ∀ time : ℝ, 0 ≤ time → time ≤ horizon →
              |(holdingJumpIndex sample.2 (acceleration depth * time) : ℝ) /
                acceleration depth - time| < tolerance) := by
  have average := (quasiMeasurePreserving_snd
    (μ := finiteDiscreteWalkLaw endpoint positiveDegree initial) (ν := exponentialHoldingTimeLaw)).ae
    exponentialHoldingTimeLaw_clock_average
  filter_upwards [finiteContinuousWalkSampleLaw_regular endpoint positiveDegree initial, average]
    with sample regular average
  constructor
  · exact fun acceleration time nonzero =>
      holdingTimePath_dePoissonization sample.1 sample.2 regular.1 acceleration time nonzero
  · intro acceleration accelerationPositive accelerationDiverges horizon horizonNonnegative tolerance tolerancePositive
    exact ⟨holdingClock_floor_uniform sample.2 average acceleration accelerationPositive accelerationDiverges
      horizon horizonNonnegative tolerance tolerancePositive,
      holdingJumpClock_uniform sample.2 regular.1 regular.2.1 average acceleration accelerationPositive
        accelerationDiverges horizon horizonNonnegative tolerance tolerancePositive⟩

end
end IGSIII34.Diffusion
