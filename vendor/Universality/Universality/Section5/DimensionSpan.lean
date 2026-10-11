import Universality.Section5.TranscendentalDimensions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic.FinCases

namespace Universality.Section5
open Submodule

theorem rational_triple_span (value : ℝ) :
    span ℚ {232 * value, 219 * value, 70 * value} = span ℚ {value} := by
  apply le_antisymm
  · apply span_le.mpr
    intro element member
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
    rcases member with rfl | rfl | rfl
    all_goals
      apply mem_span_singleton.mpr
    · exact ⟨232, by norm_num [Rat.smul_def]⟩
    · exact ⟨219, by norm_num [Rat.smul_def]⟩
    · exact ⟨70, by norm_num [Rat.smul_def]⟩
  · apply span_le.mpr
    intro element member
    rw [Set.mem_singleton_iff.mp member]
    have first : 232 * value ∈ span ℚ {232 * value, 219 * value, 70 * value} :=
      subset_span (by simp)
    have scaled := smul_mem (span ℚ {232 * value, 219 * value, 70 * value})
      (1 / 232 : ℚ) first
    simpa [Rat.smul_def, mul_assoc] using scaled

theorem rational_triple_finrank (value : ℝ) (nonzero : value ≠ 0) :
    Module.finrank ℚ (span ℚ {232 * value, 219 * value, 70 * value}) = 1 := by
  rw [rational_triple_span]
  exact finrank_span_singleton nonzero

theorem irrational_pair_independent (value : ℝ) (irrational : Irrational value) :
    LinearIndependent ℚ ![value, (1 : ℝ)] := by
  rw [linearIndependent_fin2]
  constructor
  · norm_num
  · intro rational equality
    apply irrational
    refine ⟨rational, ?_⟩
    simpa [Rat.smul_def] using equality

theorem rational_triple_with_one_span (value : ℝ) :
    span ℚ {1, 232 * value, 219 * value, 70 * value} = span ℚ {value, 1} := by
  rw [span_insert, rational_triple_span, span_insert]
  exact sup_comm _ _

theorem rational_triple_with_one_finrank (value : ℝ) (irrational : Irrational value) :
    Module.finrank ℚ (span ℚ {1, 232 * value, 219 * value, 70 * value}) = 2 := by
  rw [rational_triple_with_one_span]
  have rank := finrank_span_eq_card (irrational_pair_independent value irrational)
  rw [Matrix.range_cons_cons_empty] at rank
  exact rank

theorem shifted_dimensions_span_rank :
    Module.finrank ℚ (span ℚ
      {Real.log ((19 : ℝ) ^ 232) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ),
       Real.log ((19 : ℝ) ^ 219) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ),
       Real.log ((19 : ℝ) ^ 70) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)}) = 1 := by
  have equality :
      ({Real.log ((19 : ℝ) ^ 232) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ),
       Real.log ((19 : ℝ) ^ 219) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ),
       Real.log ((19 : ℝ) ^ 70) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)} : Set ℝ) =
      {232 * (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)),
       219 * (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)),
       70 * (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ))} := by
    simp only [Real.log_pow, Nat.cast_ofNat, mul_div_assoc]
  rw [equality]
  exact rational_triple_finrank _ (ne_of_gt (div_pos (Real.log_pos (by norm_num))
    (Real.log_pos (by exact_mod_cast shifted_scale_gt_one))))

theorem shifted_dimensions_with_one_span_rank :
    Module.finrank ℚ (span ℚ
      {1, Real.log ((19 : ℝ) ^ 232) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ),
       Real.log ((19 : ℝ) ^ 219) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ),
       Real.log ((19 : ℝ) ^ 70) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)}) = 2 := by
  have equality :
      ({1, Real.log ((19 : ℝ) ^ 232) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ),
       Real.log ((19 : ℝ) ^ 219) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ),
       Real.log ((19 : ℝ) ^ 70) / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)} : Set ℝ) =
      {1, 232 * (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)),
       219 * (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)),
       70 * (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ))} := by
    simp only [Real.log_pow, Nat.cast_ofNat, mul_div_assoc]
  rw [equality]
  exact rational_triple_with_one_finrank _ shifted_log_ratio_irrational

end Universality.Section5

