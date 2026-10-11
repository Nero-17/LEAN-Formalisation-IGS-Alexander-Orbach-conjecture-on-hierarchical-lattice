import IGSIII34.Spectral.CylinderClockUpperArithmeticCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace IGSIII34.Spectral
noncomputable section

def resistanceMeshSlackCompletion20261011 (growth : ℝ) (index : ℕ) : ℝ :=
  1 + (growth - 1) / (index + 2)

theorem resistance_mesh_slack_bounds_completion20261011
    (growth : ℝ) (greater : 1 < growth) (index : ℕ) :
    1 < resistanceMeshSlackCompletion20261011 growth index ∧
      resistanceMeshSlackCompletion20261011 growth index < growth := by
  have numerator : 0 < growth - 1 := sub_pos.mpr greater
  have denominator : 1 < (index + 2 : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) index]
  have lower := div_pos numerator (zero_lt_one.trans denominator)
  have upper := div_lt_self numerator denominator
  dsimp only [resistanceMeshSlackCompletion20261011]
  constructor <;> linarith

theorem resistance_mesh_slack_eventually_small_completion20261011
    (growth : ℝ) (greater : 1 < growth) (tolerance : ℝ) (toleranceGreater : 1 < tolerance) :
    ∃ index : ℕ, resistanceMeshSlackCompletion20261011 growth index < tolerance := by
  obtain ⟨index, large⟩ := exists_nat_gt ((growth - 1) / (tolerance - 1))
  have tolerancePositive : 0 < tolerance - 1 := sub_pos.mpr toleranceGreater
  have numerator : growth - 1 < (index : ℝ) * (tolerance - 1) := (div_lt_iff₀ tolerancePositive).mp large
  refine ⟨index, ?_⟩
  dsimp only [resistanceMeshSlackCompletion20261011]
  have divided : (growth - 1) / (index + 2 : ℝ) < tolerance - 1 :=
    (div_lt_iff₀ (by positivity : 0 < (index + 2 : ℝ))).mpr (by nlinarith)
  linarith

end
end IGSIII34.Spectral
