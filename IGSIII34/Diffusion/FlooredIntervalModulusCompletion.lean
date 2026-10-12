import IGSIII34.Diffusion.DiscreteRescaledObservationCompletion
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

theorem natFloor_difference_le_completion
    (first second : ℝ) (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) :
    |(⌊first⌋₊ : ℝ) - (⌊second⌋₊ : ℝ)| ≤ |first - second| + 1 := by
  have firstLower := Nat.floor_le firstNonnegative
  have firstUpper := Nat.lt_floor_add_one first
  have secondLower := Nat.floor_le secondNonnegative
  have secondUpper := Nat.lt_floor_add_one second
  apply abs_le.mpr
  constructor
  · linarith [neg_le_abs (first - second)]
  · linarith [le_abs_self (first - second)]

def finiteIntervalChainBadModulusCompletion {Vertex Space : Type*} [MetricSpace Space]
    (placement : Vertex → Space) (scale horizon duration tolerance : ℝ) : Set (ℕ → Vertex) :=
  {path | ∃ first ≤ ⌊scale * horizon⌋₊, ∃ second ≤ ⌊scale * horizon⌋₊,
    |(first : ℝ) - second| ≤ scale * duration + 1 ∧ tolerance < dist (placement (path first)) (placement (path second))}

theorem finiteIntervalChainBadModulus_measurable_completion
    {Vertex Space : Type*} [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    [SecondCountableTopology Space] [MeasurableSpace Vertex]
    (placement : Vertex → Space) (placementMeasurable : Measurable placement)
    (scale horizon duration tolerance : ℝ) :
    MeasurableSet (finiteIntervalChainBadModulusCompletion placement scale horizon duration tolerance) := by
  simp only [finiteIntervalChainBadModulusCompletion, setOf_exists, setOf_and]
  apply MeasurableSet.iUnion
  intro first
  apply MeasurableSet.inter (MeasurableSet.const _)
  apply MeasurableSet.iUnion
  intro second
  apply MeasurableSet.inter (MeasurableSet.const _)
  exact ((MeasurableSet.const _) : MeasurableSet {path : ℕ → Vertex | |(first : ℝ) - second| ≤ scale * duration + 1}).inter
    (measurableSet_lt measurable_const ((placementMeasurable.comp (measurable_pi_apply first)).dist
      (placementMeasurable.comp (measurable_pi_apply second))))

/-- A finite-chain index-window estimate controls every real time of the
actual floored process, including the terminal endpoint. -/
theorem finiteIntervalChain_good_modulus_completion
    {Vertex Space : Type*} [MetricSpace Space]
    (placement : Vertex → Space) (scale horizon duration tolerance : ℝ)
    (scaleNonnegative : 0 ≤ scale) (horizonNonnegative : 0 ≤ horizon)
    (path : ℕ → Vertex)
    (good : path ∉ finiteIntervalChainBadModulusCompletion placement scale horizon duration tolerance)
    (first second : Set.Icc (0 : ℝ) 1)
    (near : horizon * dist first second < duration) :
    dist (placement (path ⌊scale * horizon * (first : ℝ)⌋₊))
      (placement (path ⌊scale * horizon * (second : ℝ)⌋₊)) ≤ tolerance := by
  have productNonnegative : 0 ≤ scale * horizon := mul_nonneg scaleNonnegative horizonNonnegative
  have firstNonnegative : 0 ≤ scale * horizon * (first : ℝ) := mul_nonneg productNonnegative first.property.1
  have secondNonnegative : 0 ≤ scale * horizon * (second : ℝ) := mul_nonneg productNonnegative second.property.1
  have firstBound : ⌊scale * horizon * (first : ℝ)⌋₊ ≤ ⌊scale * horizon⌋₊ :=
    Nat.floor_mono (by simpa only [mul_one] using mul_le_mul_of_nonneg_left first.property.2 productNonnegative)
  have secondBound : ⌊scale * horizon * (second : ℝ)⌋₊ ≤ ⌊scale * horizon⌋₊ :=
    Nat.floor_mono (by simpa only [mul_one] using mul_le_mul_of_nonneg_left second.property.2 productNonnegative)
  have difference := natFloor_difference_le_completion _ _ firstNonnegative secondNonnegative
  have factor : |scale * horizon * (first : ℝ) - scale * horizon * (second : ℝ)| =
      scale * (horizon * dist first second) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg productNonnegative, Subtype.dist_eq, Real.dist_eq]
    ring
  rw [factor] at difference
  have window : |(⌊scale * horizon * (first : ℝ)⌋₊ : ℝ) - ⌊scale * horizon * (second : ℝ)⌋₊| ≤ scale * duration + 1 :=
    difference.trans (add_le_add (mul_le_mul_of_nonneg_left near.le scaleNonnegative) le_rfl)
  by_contra bad
  exact good ⟨_, firstBound, _, secondBound, window, lt_of_not_ge bad⟩

theorem finiteIntervalChainBadModulus_subset_completion
    {Vertex Space : Type*} [MetricSpace Space]
    (placement : Vertex → Space) (scale horizon duration tolerance : ℝ) :
    finiteIntervalChainBadModulusCompletion placement scale horizon duration tolerance ⊆
      {path | ∃ first last, first ≤ last ∧ last ≤ ⌊scale * horizon⌋₊ ∧
        last ≤ first + ⌈scale * duration + 1⌉₊ ∧ tolerance < dist (placement (path first)) (placement (path last))} := by
  rintro path ⟨first, firstBound, second, secondBound, window, far⟩
  have ceilBound : scale * duration + 1 ≤ (⌈scale * duration + 1⌉₊ : ℝ) := Nat.le_ceil _
  by_cases ordered : first ≤ second
  · have castOrdered : (first : ℝ) ≤ second := by exact_mod_cast ordered
    rw [abs_of_nonpos (sub_nonpos.mpr castOrdered)] at window
    have castWindow : (second : ℝ) ≤ first + (⌈scale * duration + 1⌉₊ : ℝ) := by linarith
    exact ⟨first, second, ordered, secondBound, by exact_mod_cast castWindow, far⟩
  · have orderedReverse : second ≤ first := Nat.le_of_lt (Nat.lt_of_not_ge ordered)
    have castOrdered : (second : ℝ) ≤ first := by exact_mod_cast orderedReverse
    rw [abs_of_nonneg (sub_nonneg.mpr castOrdered)] at window
    have castWindow : (first : ℝ) ≤ second + (⌈scale * duration + 1⌉₊ : ℝ) := by linarith
    exact ⟨second, first, orderedReverse, firstBound, by exact_mod_cast castWindow, by simpa only [dist_comm] using far⟩

end
end IGSIII34.Diffusion



