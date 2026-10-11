import IGSIII34.Diffusion.SkorokhodFiniteGridCompletion20261011
import Mathlib.Algebra.Order.Floor.Ring

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal

def skorokhodRegularGridPointCompletion20261011 (grid : ℕ) (index : Fin (grid + 2)) :
    SkorokhodIntervalTimeCompletion20261011 :=
  ⟨(index.val : ℝ) / (grid + 1 : ℝ), by
    have denominator : 0 < (grid + 1 : ℝ) := by positivity
    constructor
    · exact div_nonneg (Nat.cast_nonneg _) denominator.le
    · apply (div_le_one denominator).mpr
      exact_mod_cast Nat.le_of_lt_succ index.isLt⟩

def skorokhodRegularGridSelectionCompletion20261011 (grid : ℕ)
    (time : SkorokhodIntervalTimeCompletion20261011) : Fin (grid + 2) :=
  ⟨⌊(grid + 1 : ℝ) * (time : ℝ)⌋₊, by
    have bound : (grid + 1 : ℝ) * (time : ℝ) ≤ (grid + 1 : ℝ) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left time.property.2 (by positivity : 0 ≤ (grid + 1 : ℝ))
    have floorBound := Nat.floor_mono bound
    have floorCast : ⌊(grid + 1 : ℝ)⌋₊ = grid + 1 := by simpa only [Nat.cast_add, Nat.cast_one] using (Nat.floor_natCast (R := ℝ) (grid + 1))
    rw [floorCast] at floorBound
    omega⟩

theorem skorokhodRegularGridSelection_near_completion20261011 (grid : ℕ)
    (time : SkorokhodIntervalTimeCompletion20261011) :
    dist time (skorokhodRegularGridPointCompletion20261011 grid (skorokhodRegularGridSelectionCompletion20261011 grid time)) <
      1 / (grid + 1 : ℝ) := by
  have denominator : 0 < (grid + 1 : ℝ) := by positivity
  have productNonnegative : 0 ≤ (grid + 1 : ℝ) * (time : ℝ) := mul_nonneg denominator.le time.property.1
  have lower := Nat.floor_le productNonnegative
  have upper := Nat.lt_floor_add_one ((grid + 1 : ℝ) * (time : ℝ))
  change |(time : ℝ) - (⌊(grid + 1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid + 1 : ℝ)| < _
  have quotientBound : (⌊(grid + 1 : ℝ) * (time : ℝ)⌋₊ : ℝ) / (grid + 1 : ℝ) ≤ (time : ℝ) :=
    (div_le_iff₀ denominator).mpr (by simpa only [mul_comm] using lower)
  rw [abs_of_nonneg (sub_nonneg.mpr quotientBound)]
  apply (lt_div_iff₀ denominator).mpr
  rw [sub_mul, div_mul_cancel₀ _ denominator.ne']
  nlinarith

theorem skorokhodRegularGrid_mesh_tendsto_completion20261011 :
    Tendsto (fun grid : ℕ => 1 / (grid + 1 : ℝ)) atTop (𝓝 0) := by
  simpa only [Nat.cast_add, Nat.cast_one] using tendsto_one_div_add_atTop_nhds_zero_nat

end
end IGSIII34.Diffusion



