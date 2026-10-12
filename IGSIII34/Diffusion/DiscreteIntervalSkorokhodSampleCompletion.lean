import IGSIII34.Diffusion.SkorokhodFiniteGridCompletion
import IGSIII34.Diffusion.DiscreteRescaledObservationCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology NNReal

variable {Space Vertex Edge : Type*} [MetricSpace Space]
  [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space]
  [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]

def discreteIntervalSkorokhodSampleCompletion
    (scale : ℝ) (horizon : ℝ≥0) (placement : Vertex → Space) (path : ℕ → Vertex) :
    SkorokhodIntervalPathCompletion Space :=
  ⟨fun time => placement (path ⌊scale * (horizon : ℝ) * (time : ℝ)⌋₊)⟩

def discreteIntervalFloorSelectionCompletion
    (scale : ℝ) (scaleNonnegative : 0 ≤ scale) (horizon : ℝ≥0)
    (time : SkorokhodIntervalTimeCompletion) : Fin (⌊scale * (horizon : ℝ)⌋₊ + 1) :=
  ⟨⌊scale * (horizon : ℝ) * (time : ℝ)⌋₊, by
    have bound : scale * (horizon : ℝ) * (time : ℝ) ≤ scale * (horizon : ℝ) := by
      have realLE : (Real.instPreorder.toLE : LE ℝ) = Real.instLE := by rfl
      have raw := mul_le_mul_of_nonneg_left time.property.2 (mul_nonneg scaleNonnegative horizon.property)
      rw [realLE] at raw
      convert raw using 1
      · first | rfl | exact mul_right_comm scale (horizon : ℝ) (time : ℝ)
      · exact (mul_one (scale * (horizon : ℝ))).symm
    exact Nat.lt_succ_of_le (Nat.floor_mono bound)⟩

theorem discreteIntervalSkorokhodSample_reconstruction_completion
    (scale : ℝ) (scaleNonnegative : 0 ≤ scale) (horizon : ℝ≥0)
    (placement : Vertex → Space) (path : ℕ → Vertex) :
    discreteIntervalSkorokhodSampleCompletion scale horizon placement path =
      skorokhodFiniteReconstructionCompletion (discreteIntervalFloorSelectionCompletion scale scaleNonnegative horizon)
        (fun index => placement (path index.val)) := rfl

/-- A genuine accelerated jump chain is a Borel random variable in the
time-change path topology: on every bounded interval it is reconstructed
from a finite, measurable walk prefix. -/
theorem discreteIntervalSkorokhodSample_measurable_completion
    (scale : ℝ) (scaleNonnegative : 0 ≤ scale) (horizon : ℝ≥0) (placement : Vertex → Space) :
    Measurable (discreteIntervalSkorokhodSampleCompletion scale horizon placement) := by
  change Measurable (fun path : ℕ → Vertex =>
    skorokhodFiniteReconstructionCompletion (discreteIntervalFloorSelectionCompletion scale scaleNonnegative horizon)
      (fun index => placement (path index.val)))
  exact skorokhod_reconstructed_sample_measurable_completion _ _
    (measurable_pi_lambda _ fun index => (measurable_of_finite placement).comp (measurable_pi_apply index.val))

def discreteIntervalSkorokhodProbabilityCompletion
    [DecidableEq Vertex] [Fintype Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (scale : ℝ) (scaleNonnegative : 0 ≤ scale)
    (horizon : ℝ≥0) (placement : Vertex → Space) :
    ProbabilityMeasure (SkorokhodIntervalPathCompletion Space) :=
  (discreteWalkProbabilityCompletion endpoint positiveDegree initial).map
    (discreteIntervalSkorokhodSample_measurable_completion scale scaleNonnegative horizon placement).aemeasurable

end
end IGSIII34.Diffusion










