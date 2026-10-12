import IGSIII34.Diffusion.FlooredIntervalModulusCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

theorem finiteChain_good_realTime_modulus_completion
    {Vertex Space : Type*} [MetricSpace Space]
    (placement : Vertex → Space) (scale horizon duration tolerance : ℝ)
    (scaleNonnegative : 0 ≤ scale) (path : ℕ → Vertex)
    (good : path ∉ finiteIntervalChainBadModulusCompletion placement scale horizon duration tolerance)
    (first second : ℝ≥0) (firstBound : (first : ℝ) ≤ horizon) (secondBound : (second : ℝ) ≤ horizon)
    (near : dist first second < duration) :
    dist (placement (path ⌊scale * (first : ℝ)⌋₊)) (placement (path ⌊scale * (second : ℝ)⌋₊)) ≤ tolerance := by
  have firstIndexBound := Nat.floor_mono (mul_le_mul_of_nonneg_left firstBound scaleNonnegative)
  have secondIndexBound := Nat.floor_mono (mul_le_mul_of_nonneg_left secondBound scaleNonnegative)
  have difference := natFloor_difference_le_completion _ _
    (mul_nonneg scaleNonnegative first.property) (mul_nonneg scaleNonnegative second.property)
  have factor : |scale * (first : ℝ) - scale * (second : ℝ)| = scale * dist first second := by
    rw [← mul_sub, abs_mul, abs_of_nonneg scaleNonnegative, NNReal.dist_eq]
  have rewritten : |(⌊scale * (first : ℝ)⌋₊ : ℝ) - ⌊scale * (second : ℝ)⌋₊| ≤ scale * dist first second + 1 := by
    calc
      _ ≤ |scale * (first : ℝ) - scale * (second : ℝ)| + 1 := difference
      _ = _ := congrArg (fun number : ℝ => number + 1) factor
  have window := rewritten.trans (add_le_add (mul_le_mul_of_nonneg_left near.le scaleNonnegative) le_rfl)
  by_contra bad
  exact good ⟨_, firstIndexBound, _, secondIndexBound, window, lt_of_not_ge bad⟩

end
end IGSIII34.Diffusion

