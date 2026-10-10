import IGSIII.Geometry.UniformRadiusBound
import IGSIII.Geometry.DescendantEnvelope

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped ENNReal Topology BigOperators

/-- The precise probabilistic input for full-cluster mesh is one sufficiently
high moment of a terminal-distance envelope. Actual component radii, including
both B sides and every dangling branch, then decay uniformly over all remaining
depths. No component-diameter convergence or mesh certificate is assumed. -/
theorem ae_uniform_actual_component_mesh (rule : Rule)
    (probability : Measure (((List (Fin rule.edges) × Bool) → Configuration rule.edges)))
    (scale eta : ℝ) (scale_gt_one : 1 < scale) (eta_positive : 0 < eta) (eta_lt_one : eta < 1)
    (growth_ge_one : 1 ≤ scale * eta)
    (power : ℕ) (power_positive : 0 < power) (moment_growth : (rule.edges : ℝ) < (scale * eta) ^ power)
    (envelope : List (Fin rule.edges) → Bool →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (measurable : ∀ address opened, AEStronglyMeasurable (envelope address opened) probability)
    (bound : ℝ≥0∞) (bound_finite : bound ≠ ∞)
    (moment_bound : ∀ address opened, eLpNorm (envelope address opened) power probability ≤ bound)
    (terminal_bound : ∀ᵐ marks ∂probability, ∀ address opened depth,
      (markedTerminalDistance rule marks depth address opened : ℝ) / scale ^ (depth + 1) ≤
        envelope address opened marks) :
    ∀ᵐ marks ∂probability, ∃ start : ℕ, ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) /
          scale ^ (depth + 1 + address.length) ≤
        ((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ address.length := by
  have scale_positive := zero_lt_one.trans scale_gt_one
  have growth_positive := mul_pos scale_positive eta_positive
  have decay : (rule.edges : ℝ≥0∞) * (ENNReal.ofReal (scale * eta))⁻¹ ^ power < 1 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_inv_of_pos growth_positive,
      ← ENNReal.ofReal_pow (inv_nonneg.mpr growth_positive.le),
      ← ENNReal.ofReal_mul (Nat.cast_nonneg rule.edges)]
    apply ENNReal.ofReal_lt_one.mpr
    rw [inv_pow, ← div_eq_mul_inv]
    exact (div_lt_one (pow_pos growth_positive power)).mpr moment_growth
  have descendants := ae_descendant_envelope_exponential rule.edges power power_positive envelope measurable bound
    (ENNReal.ofReal (scale * eta)) bound_finite (ENNReal.ofReal_ne_zero_iff.mpr growth_positive)
    ENNReal.ofReal_ne_top moment_bound decay
  filter_upwards [descendants, terminal_bound] with marks descendants terminal_bound
  obtain ⟨start, small⟩ := eventually_atTop.mp descendants
  have address_bound (address : List (Fin rule.edges)) (opened : Bool) (beyond : start ≤ address.length) :
      envelope address opened marks ≤ (scale * eta) ^ address.length := by
    have small_word := small address.length beyond address.get opened
    rw [List.ofFn_get] at small_word
    have abs_bound : |envelope address opened marks| < (scale * eta) ^ address.length := by
      apply (ENNReal.ofReal_lt_ofReal_iff (pow_pos growth_positive address.length)).mp
      simpa only [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow growth_positive.le] using small_word
    exact (le_abs_self (envelope address opened marks)).trans abs_bound.le
  have coefficient_large : (rule.edges : ℝ) ≤ (rule.edges + 1 : ℝ) / (1 - eta) := by
    apply (le_div_iff₀ (sub_pos.mpr eta_lt_one)).mpr
    nlinarith [show (0 : ℝ) ≤ (rule.edges : ℝ) from Nat.cast_nonneg _]
  have coefficient_contracts : eta * ((rule.edges + 1 : ℝ) / (1 - eta) + rule.edges) ≤
      (rule.edges + 1 : ℝ) / (1 - eta) := by
    have formula : ((rule.edges + 1 : ℝ) / (1 - eta)) * (1 - eta) = rule.edges + 1 :=
      div_mul_cancel₀ _ (sub_pos.mpr eta_lt_one).ne'
    have edges_bound : eta * rule.edges ≤ (rule.edges : ℝ) :=
      mul_le_of_le_one_left (Nat.cast_nonneg _) eta_lt_one.le
    nlinarith
  have uniform_radius := marked_radius_uniform_bound_of_terminal_envelope rule marks scale eta
    ((rule.edges + 1 : ℝ) / (1 - eta)) start scale_gt_one eta_positive growth_ge_one coefficient_large coefficient_contracts
    (fun address opened depth beyond => by
      have normalized := (terminal_bound address opened depth).trans (address_bound address opened beyond)
      simpa only [mul_comm] using (div_le_iff₀ (pow_pos scale_positive (depth + 1))).mp normalized)
  refine ⟨start, ?_⟩
  intro address opened depth beyond
  calc
    _ ≤ (((rule.edges + 1 : ℝ) / (1 - eta)) * scale ^ (depth + 1) * (scale * eta) ^ address.length) /
        scale ^ (depth + 1 + address.length) :=
      div_le_div_of_nonneg_right (uniform_radius depth address opened beyond) (pow_pos scale_positive _).le
    _ = _ := by
      rw [pow_add, mul_pow]
      field_simp [scale_positive.ne'] <;> ring

end IGSIII.Geometry
