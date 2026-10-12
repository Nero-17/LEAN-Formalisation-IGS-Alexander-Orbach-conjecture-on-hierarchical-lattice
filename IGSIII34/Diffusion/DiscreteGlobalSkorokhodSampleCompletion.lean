import IGSIII34.Diffusion.SkorokhodGlobalWeakConvergenceCompletion
import IGSIII34.Diffusion.FlooredIntervalModulusCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal
variable {Space Vertex Edge : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]
  [MeasurableSpace Vertex] [Fintype Vertex] [MeasurableSingletonClass Vertex]

def discreteGlobalSkorokhodSampleCompletion (scale : ℝ)
    (placement : Vertex → Space) (path : ℕ → Vertex) : SkorokhodGlobalPathCompletion Space :=
  skorokhodGlobalFloorReconstructionCompletion scale (fun index => placement (path index))

theorem discreteGlobalSkorokhodSample_measurable_completion
    (scale : ℝ) (scaleNonnegative : 0 ≤ scale) (placement : Vertex → Space) :
    Measurable (discreteGlobalSkorokhodSampleCompletion scale placement) :=
  (skorokhodGlobalFloorReconstruction_measurable_completion scale scaleNonnegative).comp
    (measurable_pi_lambda _ fun index => (measurable_of_finite placement).comp (measurable_pi_apply index))

def discreteGlobalSkorokhodProbabilityCompletion [DecidableEq Vertex] [Fintype Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : ProbabilityMeasure Vertex) (scale : ℝ) (scaleNonnegative : 0 ≤ scale)
    (placement : Vertex → Space) : ProbabilityMeasure (SkorokhodGlobalPathCompletion Space) :=
  (discreteWalkProbabilityCompletion endpoint positiveDegree initial).map
    (discreteGlobalSkorokhodSample_measurable_completion scale scaleNonnegative placement).aemeasurable

theorem finiteGlobalChain_good_modulus_completion
    (placement : Vertex → Space) (scale horizon duration tolerance : ℝ)
    (scaleNonnegative : 0 ≤ scale) (path : ℕ → Vertex)
    (good : path ∉ finiteIntervalChainBadModulusCompletion placement scale horizon duration tolerance)
    (first second : ℝ≥0) (firstBefore : (first : ℝ) ≤ horizon) (secondBefore : (second : ℝ) ≤ horizon)
    (near : dist first second < duration) :
    dist (placement (path ⌊scale * (first : ℝ)⌋₊)) (placement (path ⌊scale * (second : ℝ)⌋₊)) ≤ tolerance := by
  have firstBound := Nat.floor_mono (mul_le_mul_of_nonneg_left firstBefore scaleNonnegative)
  have secondBound := Nat.floor_mono (mul_le_mul_of_nonneg_left secondBefore scaleNonnegative)
  have difference := natFloor_difference_le_completion
    (scale * (first : ℝ)) (scale * (second : ℝ))
    (mul_nonneg scaleNonnegative first.property) (mul_nonneg scaleNonnegative second.property)
  have factor : |scale * (first : ℝ) - scale * (second : ℝ)| = scale * dist first second := by
    rw [← mul_sub, abs_mul, abs_of_nonneg scaleNonnegative]
    rfl
  rw [factor] at difference
  have window := difference.trans (add_le_add (mul_le_mul_of_nonneg_left near.le scaleNonnegative) le_rfl)
  by_contra bad
  exact good ⟨_, firstBound, _, secondBound, window, lt_of_not_ge bad⟩

end
end IGSIII34.Diffusion
