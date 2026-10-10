import Universality.Arithmetic.DimensionRank
import Mathlib.NumberTheory.Real.Irrational

namespace Universality.Section4

theorem linearIndependent_one_irrational {dimension : ℝ}
    (hirrational : Irrational dimension) : LinearIndependent ℚ ![1, dimension] := by
  apply (LinearIndependent.pair_iff' (one_ne_zero : (1 : ℝ) ≠ 0)).mpr
  intro coefficient heq
  apply hirrational
  exact ⟨coefficient, by simpa only [Rat.smul_def, smul_eq_mul, mul_one] using heq⟩

theorem not_three_independent_scale_logs {dimension : ℝ}
    (hirrational : Irrational dimension) (scales : Fin 3 → ℕ)
    (hscales : ∀ i, 1 < scales i)
    (halgebraic : ∀ i, IsAlgebraic ℚ
      (Real.exp (Real.log (scales i : ℝ) * dimension))) :
    ¬ LinearIndependent ℚ (fun i => Real.log (scales i : ℝ)) := by
  apply not_linearIndependent_of_algebraic_real_exponentials ![1, dimension]
    (fun i => Real.log (scales i : ℝ)) (linearIndependent_one_irrational hirrational)
  intro i j
  fin_cases i
  · change IsAlgebraic ℚ (Real.exp (1 * Real.log (scales j : ℝ)))
    rw [one_mul, Real.exp_log (by exact_mod_cast (lt_trans Nat.zero_lt_one (hscales j)))]
    simpa using (isAlgebraic_algebraMap (A := ℝ) (scales j : ℚ))
  · change IsAlgebraic ℚ (Real.exp (dimension * Real.log (scales j : ℝ)))
    simpa only [mul_comm dimension] using halgebraic j

/-- This is a bound on cardinal rank, so it also rules out an infinite-dimensional
span. It is not the vacuous `finrank = 0` convention for infinite dimension. -/
theorem scale_log_rank_le_two {ι : Type*} {dimension : ℝ}
    (hirrational : Irrational dimension) (scales : ι → ℕ)
    (hscales : ∀ i, 1 < scales i)
    (halgebraic : ∀ i, IsAlgebraic ℚ
      (Real.exp (Real.log (scales i : ℝ) * dimension))) :
    Module.rank ℚ (Submodule.span ℚ (Set.range (fun i => Real.log (scales i : ℝ)))) ≤ 2 := by
  classical
  obtain ⟨basis, hsubset, hspan, hindependent⟩ :=
    exists_linearIndependent ℚ (Set.range (fun i => Real.log (scales i : ℝ)))
  have hrank : Module.rank ℚ (Submodule.span ℚ
      (Set.range (fun i => Real.log (scales i : ℝ)))) = Cardinal.mk basis := by
    rw [← hspan]
    exact rank_span_set hindependent
  rw [hrank]
  by_contra hcard
  have hthree : (3 : Cardinal) ≤ Cardinal.mk basis := by
    calc
      (3 : Cardinal) = ((2 + 1 : ℕ) : Cardinal) := rfl
      _ = (2 : Cardinal) + 1 := by rw [Nat.cast_add, Nat.cast_one]; rfl
      _ ≤ Cardinal.mk basis := Cardinal.natCast_add_one_le_iff.mpr (lt_of_not_ge hcard)
  have hexists : Nonempty (Fin 3 ↪ basis) := by
    apply (Cardinal.le_def (Fin 3) basis).mp
    simpa using hthree
  obtain ⟨embedding⟩ := hexists
  have hselected : ∀ j : Fin 3, ∃ i, Real.log (scales i : ℝ) = (embedding j : ℝ) :=
    fun j => hsubset (embedding j).property
  choose indices hindices using hselected
  have hlogs : (fun j => Real.log (scales (indices j) : ℝ)) =
      ((↑) : basis → ℝ) ∘ embedding := funext hindices
  apply not_three_independent_scale_logs hirrational (scales ∘ indices)
    (fun j => hscales (indices j)) (fun j => halgebraic (indices j))
  change LinearIndependent ℚ (fun j => Real.log (scales (indices j) : ℝ))
  rw [hlogs]
  exact hindependent.comp embedding embedding.injective

end Universality.Section4

#print axioms Universality.Section4.scale_log_rank_le_two
