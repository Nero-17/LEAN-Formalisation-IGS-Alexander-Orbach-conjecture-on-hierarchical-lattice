import IGSIII.Mass.BorelCantelli
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

variable {Ω : Type*} [MeasurableSpace Ω] {probability : Measure Ω}

/-- A uniform high moment controls all descendants at once. Only marginal
moment bounds are used; sibling types and envelopes need not be independent. -/
theorem ae_descendant_envelope_exponential (edges power : ℕ) (power_positive : 0 < power)
    (envelope : List (Fin edges) → Bool → Ω → ℝ)
    (measurable : ∀ address opened, AEStronglyMeasurable (envelope address opened) probability)
    (bound growth : ℝ≥0∞) (bound_finite : bound ≠ ∞)
    (growth_nonzero : growth ≠ 0) (growth_finite : growth ≠ ∞)
    (moment_bound : ∀ address opened, eLpNorm (envelope address opened) power probability ≤ bound)
    (decay : (edges : ℝ≥0∞) * growth⁻¹ ^ power < 1) :
    ∀ᵐ sample ∂probability, ∀ᶠ depth in atTop,
      ∀ (word : Fin depth → Fin edges) (opened : Bool),
        ‖envelope (List.ofFn word) opened sample‖ₑ < growth ^ depth := by
  have single_estimate (depth : ℕ) (word : Fin depth → Fin edges) (opened : Bool) :
      probability {sample | growth ^ depth ≤ ‖envelope (List.ofFn word) opened sample‖ₑ} ≤
        (growth ^ depth)⁻¹ ^ power * bound ^ power := by
    have estimate := meas_ge_le_mul_pow_eLpNorm_enorm probability
      (show (power : ℝ≥0∞) ≠ 0 by exact_mod_cast power_positive.ne') (by simp)
      (measurable (List.ofFn word) opened) (pow_ne_zero depth growth_nonzero)
      (by simp [ENNReal.pow_ne_top growth_finite])
    simp only [ENNReal.toReal_natCast, ENNReal.rpow_natCast] at estimate
    exact estimate.trans (mul_le_mul_left' (pow_le_pow_left' (moment_bound _ _) power) _)
  have estimate (depth : ℕ) :
      probability {sample | ∃ (word : Fin depth → Fin edges) (opened : Bool),
        growth ^ depth ≤ ‖envelope (List.ofFn word) opened sample‖ₑ} ≤
      (2 * bound ^ power) * ((edges : ℝ≥0∞) * growth⁻¹ ^ power) ^ depth := by
    calc
      _ = probability (⋃ word : Fin depth → Fin edges, ⋃ opened : Bool,
          {sample | growth ^ depth ≤ ‖envelope (List.ofFn word) opened sample‖ₑ}) := by
        congr 1
        ext sample
        simp
      _ ≤ ∑ word : Fin depth → Fin edges, ∑ opened : Bool,
          probability {sample | growth ^ depth ≤ ‖envelope (List.ofFn word) opened sample‖ₑ} := by
        exact (measure_iUnion_fintype_le probability _).trans
          (Finset.sum_le_sum (fun word _ => measure_iUnion_fintype_le probability _))
      _ ≤ ∑ _word : Fin depth → Fin edges, ∑ _opened : Bool,
          (growth ^ depth)⁻¹ ^ power * bound ^ power :=
        Finset.sum_le_sum (fun word _ => Finset.sum_le_sum (fun opened _ => single_estimate depth word opened))
      _ = (2 * bound ^ power) * ((edges : ℝ≥0∞) * growth⁻¹ ^ power) ^ depth := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, Fintype.card_fun,
          Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, ENNReal.inv_pow]
        rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm depth power]
        ring
  have finite_sum : (∑' depth, probability {sample | ∃ (word : Fin depth → Fin edges) (opened : Bool),
      growth ^ depth ≤ ‖envelope (List.ofFn word) opened sample‖ₑ}) ≠ ∞ := by
    apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum estimate)
    rw [ENNReal.tsum_mul_left]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top bound_finite))
      (tsum_geometric_lt_top.mpr decay).ne
  simpa only [Set.mem_setOf_eq, not_exists, not_le] using ae_eventually_notMem finite_sum

end IGSIII.Geometry
