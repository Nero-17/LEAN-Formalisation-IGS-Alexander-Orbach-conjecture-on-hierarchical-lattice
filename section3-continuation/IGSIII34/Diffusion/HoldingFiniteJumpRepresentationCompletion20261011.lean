import IGSIII34.Diffusion.HoldingTimePaths
import IGSIII34.Diffusion.JumpCountProbabilities
import IGSIII34.Diffusion.SkorokhodFiniteJumpAlignmentCompletion20261011
import Mathlib.Data.Fin.Embedding

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology BigOperators

theorem holdingTimePath_finite_interior_jump_representation_completion20261011
    {Space : Type*} [MetricSpace Space] (trajectory : ℕ → Space)
    (holdingTimes : ℕ → ℝ) (positive : ∀ index, 0 < holdingTimes index)
    (nonexplosion : Tendsto (cumulativeHoldingTime holdingTimes) atTop atTop)
    (horizon : ℝ) (horizonPositive : 0 < horizon) :
    ∃ count : ℕ, ∃ knots : Fin count → SkorokhodIntervalTimeCompletion20261011,
      StrictMono knots ∧
      (∀ index, 0 < (knots index).val ∧ (knots index).val < 1) ∧
      ∀ point : SkorokhodIntervalTimeCompletion20261011, point.val < 1 →
        holdingTimePath trajectory holdingTimes (horizon * point.val) =
          finiteJumpIntervalPathCompletion20261011 knots (fun index : Fin (count + 1) => trajectory index.val) point := by
  classical
  have strict : StrictMono (cumulativeHoldingTime holdingTimes) := by
    apply strictMono_nat_of_lt_succ
    intro index
    simp only [cumulativeHoldingTime, Finset.sum_range_succ]
    exact lt_add_of_pos_right _ (positive index)
  obtain ⟨large, reachedLarge⟩ := (nonexplosion.eventually_ge_atTop horizon).exists
  have reached : ∃ count, horizon ≤ cumulativeHoldingTime holdingTimes (count + 1) :=
    ⟨large, reachedLarge.trans (strict.monotone (Nat.le_succ large))⟩
  let count := Nat.find reached
  have below (index : Fin count) : cumulativeHoldingTime holdingTimes (index.val + 1) < horizon :=
    lt_of_not_ge (Nat.find_min reached index.isLt)
  have afterZero (index : Fin count) : 0 < cumulativeHoldingTime holdingTimes (index.val + 1) := by
    have increase := strict (Nat.zero_lt_succ index.val)
    simpa [cumulativeHoldingTime] using increase
  let knots : Fin count → SkorokhodIntervalTimeCompletion20261011 := fun index =>
    ⟨cumulativeHoldingTime holdingTimes (index.val + 1) / horizon,
      (div_pos (afterZero index) horizonPositive).le,
      (div_lt_one₀ horizonPositive).mpr (below index) |>.le⟩
  have knotsIncreasing : StrictMono knots := by
    intro first second ordered
    change cumulativeHoldingTime holdingTimes (first.val + 1) / horizon < cumulativeHoldingTime holdingTimes (second.val + 1) / horizon
    exact div_lt_div_of_pos_right (strict (by omega)) horizonPositive
  refine ⟨count, knots, knotsIncreasing, ?_, ?_⟩
  · intro index
    exact ⟨div_pos (afterZero index) horizonPositive, (div_lt_one₀ horizonPositive).mpr (below index)⟩
  · intro point beforeEndpoint
    let jump := holdingJumpIndex holdingTimes (horizon * point.val)
    have timeNonnegative : 0 ≤ horizon * point.val := mul_nonneg horizonPositive.le point.property.1
    have beforeHorizon : horizon * point.val < horizon := by nlinarith
    have interval := holdingJumpIndex_interval holdingTimes (fun index => (positive index).le) nonexplosion
      (horizon * point.val) timeNonnegative
    have jumpBound : jump ≤ count := by
      by_contra failure
      have indexBound : count + 1 ≤ jump := by omega
      have afterHorizon : horizon ≤ cumulativeHoldingTime holdingTimes jump :=
        (Nat.find_spec reached).trans (strict.monotone indexBound)
      exact (not_le_of_gt beforeHorizon) (afterHorizon.trans interval.1)
    have comparison (index : Fin count) : knots index ≤ point ↔ index.val < jump := by
      change cumulativeHoldingTime holdingTimes (index.val + 1) / horizon ≤ point.val ↔ index.val < jump
      rw [div_le_iff₀ horizonPositive, mul_comm point.val horizon]
      rw [← holdingJumpIndex_ge_iff holdingTimes positive nonexplosion (horizon * point.val) timeNonnegative (index.val + 1)]
      omega
    have filtered : (Finset.univ.filter (fun index : Fin count => knots index ≤ point)) =
        (Finset.univ : Finset (Fin jump)).map (Fin.castLEEmb jumpBound) := by
      apply Finset.ext
      intro index
      constructor
      · intro member
        apply Finset.mem_map.mpr
        refine ⟨⟨index.val, (comparison index).mp (Finset.mem_filter.mp member).2⟩, Finset.mem_univ _, ?_⟩
        exact Fin.ext rfl
      · intro member
        obtain ⟨selected, _, equality⟩ := Finset.mem_map.mp member
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [← equality]
        exact (comparison _).mpr selected.isLt
    have countEquality : finiteJumpCountCompletion20261011 knots point = jump := by
      unfold finiteJumpCountCompletion20261011
      rw [filtered, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    unfold holdingTimePath finiteJumpIntervalPathCompletion20261011
    change trajectory jump = trajectory (finiteJumpCountCompletion20261011 knots point)
    rw [countEquality]

end
end IGSIII34.Diffusion
