import IGSIII34.Diffusion.IntervalOneKnotCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Diffusion
noncomputable section
open Set
open scoped Topology

def intervalScaledTime (terminal time : SkorokhodIntervalTimeCompletion20261011) :
    SkorokhodIntervalTimeCompletion20261011 :=
  ⟨terminal.val * time.val,
    ⟨mul_nonneg terminal.property.1 time.property.1,
      (mul_le_mul_of_nonneg_left time.property.2 terminal.property.1).trans (by simpa using terminal.property.2)⟩⟩

theorem intervalScaledTime_le_terminal
    (terminal time : SkorokhodIntervalTimeCompletion20261011) :
    intervalScaledTime terminal time ≤ terminal := by
  change terminal.val * time.val ≤ terminal.val
  simpa only [mul_one] using mul_le_mul_of_nonneg_left time.property.2 terminal.property.1

def intervalRestrictedOrderIso
    (change : SkorokhodIntervalTimeCompletion20261011 ≃o SkorokhodIntervalTimeCompletion20261011)
    (terminal : SkorokhodIntervalTimeCompletion20261011) (positive : 0 < terminal.val)
    (fixed : change terminal = terminal) :
    SkorokhodIntervalTimeCompletion20261011 ≃o SkorokhodIntervalTimeCompletion20261011 where
  toFun time := ⟨(change (intervalScaledTime terminal time)).val / terminal.val, by
    constructor
    · exact div_nonneg (change _).property.1 positive.le
    · apply (div_le_one positive).mpr
      have upper := change.monotone (intervalScaledTime_le_terminal terminal time)
      rwa [fixed] at upper⟩
  invFun time := ⟨(change.symm (intervalScaledTime terminal time)).val / terminal.val, by
    constructor
    · exact div_nonneg (change.symm _).property.1 positive.le
    · apply (div_le_one positive).mpr
      have upper := change.symm.monotone (intervalScaledTime_le_terminal terminal time)
      have inverseFixed : change.symm terminal = terminal := (change.symm_apply_eq).mpr fixed.symm
      rwa [inverseFixed] at upper⟩
  left_inv time := by
    apply Subtype.ext
    have scaled : intervalScaledTime terminal
        ⟨(change (intervalScaledTime terminal time)).val / terminal.val, by
          constructor
          · exact div_nonneg (change _).property.1 positive.le
          · apply (div_le_one positive).mpr
            have upper := change.monotone (intervalScaledTime_le_terminal terminal time)
            rwa [fixed] at upper⟩ = change (intervalScaledTime terminal time) := by
      apply Subtype.ext
      exact mul_div_cancel₀ _ positive.ne'
    change (change.symm (intervalScaledTime terminal _)).val / terminal.val = time.val
    rw [scaled, change.symm_apply_apply]
    change terminal.val * time.val / terminal.val = time.val
    exact mul_div_cancel_left₀ _ positive.ne'
  right_inv time := by
    apply Subtype.ext
    have inverseFixed : change.symm terminal = terminal := (change.symm_apply_eq).mpr fixed.symm
    have scaled : intervalScaledTime terminal
        ⟨(change.symm (intervalScaledTime terminal time)).val / terminal.val, by
          constructor
          · exact div_nonneg (change.symm _).property.1 positive.le
          · apply (div_le_one positive).mpr
            have upper := change.symm.monotone (intervalScaledTime_le_terminal terminal time)
            rwa [inverseFixed] at upper⟩ = change.symm (intervalScaledTime terminal time) := by
      apply Subtype.ext
      exact mul_div_cancel₀ _ positive.ne'
    change (change (intervalScaledTime terminal _)).val / terminal.val = time.val
    rw [scaled, change.apply_symm_apply]
    change terminal.val * time.val / terminal.val = time.val
    exact mul_div_cancel_left₀ _ positive.ne'
  map_rel_iff' := by
    intro first last
    change (change (intervalScaledTime terminal first)).val / terminal.val ≤
      (change (intervalScaledTime terminal last)).val / terminal.val ↔ first ≤ last
    rw [div_le_div_iff_of_pos_right positive]
    change change (intervalScaledTime terminal first) ≤ change (intervalScaledTime terminal last) ↔ first ≤ last
    rw [change.le_iff_le]
    change terminal.val * first.val ≤ terminal.val * last.val ↔ first.val ≤ last.val
    exact mul_le_mul_iff_of_pos_left positive

theorem intervalRestrictedOrderIso_scaled_apply
    (change : SkorokhodIntervalTimeCompletion20261011 ≃o SkorokhodIntervalTimeCompletion20261011)
    (terminal : SkorokhodIntervalTimeCompletion20261011) (positive : 0 < terminal.val)
    (fixed : change terminal = terminal) (time : SkorokhodIntervalTimeCompletion20261011) :
    intervalScaledTime terminal (intervalRestrictedOrderIso change terminal positive fixed time) =
      change (intervalScaledTime terminal time) := by
  apply Subtype.ext
  exact mul_div_cancel₀ _ positive.ne'

end
end IGSIII34.Diffusion
