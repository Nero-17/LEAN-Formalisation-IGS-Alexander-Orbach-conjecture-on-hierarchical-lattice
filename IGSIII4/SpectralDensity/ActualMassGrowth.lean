import IGSIII4.SpectralDensity.ActualCritical
import IGSIII4.SpectralDensity.ActualMassProbability
import IGSIII4.SpectralDensity.EndpointTests
import IGSIII4.SpectralDensity.CoarseMassGrowth
import IGSIII4.AlexanderOrbach

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork Filter Topology

/-- Each finite rule uses its own interior reliability fixed point. -/
def appendixCriticalProbability (base : ℝ) (length : ℕ) : ℝ :=
  if lengthLarge : 2 ≤ length then
    Classical.choose (appendixRule_own_fixed_point base length lengthLarge)
  else 1 / 2

theorem appendixCriticalProbability_spec (base : ℝ) (length : ℕ) (lengthLarge : 2 ≤ length) :
    0 < appendixCriticalProbability base length ∧
      appendixCriticalProbability base length < 1 ∧
      (appendixRule base length).network.reliability (appendixCriticalProbability base length) =
        appendixCriticalProbability base length := by
  simp only [appendixCriticalProbability, dif_pos lengthLarge]
  exact Classical.choose_spec (appendixRule_own_fixed_point base length lengthLarge)

theorem appendixCriticalProbability_interval_eventually (base : ℝ) (baseAboveOne : 1 < base) :
    ∀ᶠ length : ℕ in atTop,
      7 / 10 < appendixCriticalProbability base length ∧
        appendixCriticalProbability base length < 4 / 5 := by
  filter_upwards [endpoint_lower_test_eventually base baseAboveOne,
    endpoint_upper_test_eventually base baseAboveOne, eventually_ge_atTop (2 : ℕ)] with length lower upper lengthLarge
  obtain ⟨positive, belowOne, fixedPoint⟩ := appendixCriticalProbability_spec base length lengthLarge
  apply critical_interval_from_endpoint_tests (blockCount base length) (pathCount length) (length - 2)
    (appendixCriticalProbability base length) positive belowOne fixedPoint
  · simpa only [Nat.sub_add_cancel lengthLarge] using lower
  · simpa only [Nat.sub_add_cancel lengthLarge] using upper

theorem appendix_actual_mass_bounds (base : ℝ) (length : ℕ) (lengthLarge : 2 ≤ length)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : (appendixRule base length).network.reliability probability = probability)
    (aboveHalf : 1 / 2 ≤ probability) :
    (1 / 3 : ℝ) * (blockCount base length : ℝ) * (pathCount length : ℝ) ≤
        actualMassGrowth (appendixRule base length) probability ∧
      actualMassGrowth (appendixRule base length) probability ≤
        4 + (blockCount base length : ℝ) * (pathCount length : ℝ) * (length : ℝ) := by
  have connectedLower := actual_connected_mass_lower (blockCount base length) (pathCount length)
    (length - 2) probability positive belowOne fixedPoint
  have radiusLower := (appendixRule_classical base length lengthLarge).mass_spectralRadius_strictly_gt_connected_entry positive belowOne
  have radiusUpper := (appendixRule_classical base length lengthLarge).mass_spectralRadius_lt_edges probability positive belowOne
  have coefficientLower : (1 / 3 : ℝ) ≤ probability / (1 + probability) := by
    apply (le_div_iff₀ (by positivity : 0 < 1 + probability)).mpr
    linarith
  constructor
  · have scaledLower := mul_le_mul_of_nonneg_left coefficientLower
      (by positivity : 0 ≤ ((blockCount base length * pathCount length : ℕ) : ℝ))
    have bound := scaledLower.trans (connectedLower.trans radiusLower.le)
    simpa only [Nat.cast_mul, actualMassGrowth, mul_assoc, mul_comm, mul_left_comm] using bound
  · calc
      _ ≤ ((appendixRule base length).edges : ℝ) := radiusUpper.le
      _ = _ := by
        rw [appendixRule_edges base length lengthLarge]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, blockCount, pathCount]

theorem appendix_actual_mass_normalized_log_limit (base : ℝ) (baseAboveOne : 1 < base) :
    Tendsto (fun length => Real.log (actualMassGrowth (appendixRule base length)
      (appendixCriticalProbability base length)) / (length : ℝ))
      atTop (𝓝 (Real.log base + Real.log (4 / 3 : ℝ))) := by
  apply mass_normalized_log_limit_of_edge_count_bound base baseAboveOne
  filter_upwards [appendixCriticalProbability_interval_eventually base baseAboveOne,
    eventually_ge_atTop (2 : ℕ)] with length interval lengthLarge
  obtain ⟨positive, belowOne, fixedPoint⟩ := appendixCriticalProbability_spec base length lengthLarge
  exact appendix_actual_mass_bounds base length lengthLarge _ positive belowOne fixedPoint (by linarith [interval.1])

end
end IGSIII4.SpectralDensity.ActualFamily
