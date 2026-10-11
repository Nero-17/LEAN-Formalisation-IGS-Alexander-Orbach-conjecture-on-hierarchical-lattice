import Universality.Section5.DimensionSpan

/-!
The conditional implication in the discussion of Section 5. The four
exponentials conjecture is a proposition here, never an axiom or a proved
theorem. Algebraicity of the actual responses is supplied explicitly.
-/

namespace Universality.Section5

def FourExponentialsReal : Prop :=
  ∀ first second : Fin 2 → ℝ,
    LinearIndependent ℚ first → LinearIndependent ℚ second →
      ∃ i j, Transcendental ℚ (Real.exp (first i * second j))

theorem incommensurate_scale_logs_independent {first second : ℕ}
    (first_gt_one : 1 < first) (second_gt_one : 1 < second)
    (incommensurate : ¬ ScaleCommensurate first second) :
    LinearIndependent ℚ ![Real.log (first : ℝ), Real.log (second : ℝ)] := by
  rw [linearIndependent_fin2]
  have second_log_nonzero : Real.log (second : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast second_gt_one))
  refine ⟨second_log_nonzero, ?_⟩
  intro rational equality
  apply incommensurate
  apply rational_log_ratio_commensurate first_gt_one second_gt_one
  refine ⟨rational, (div_eq_iff second_log_nonzero).mpr ?_⟩
  simpa [Rat.smul_def] using equality.symm

theorem common_irrational_dimension_obstructs_four_exponentials
    {first second : ℕ} {firstResponse secondResponse dimension : ℝ}
    (first_gt_one : 1 < first) (second_gt_one : 1 < second)
    (first_positive : 0 < firstResponse) (second_positive : 0 < secondResponse)
    (first_algebraic : IsAlgebraic ℚ firstResponse)
    (second_algebraic : IsAlgebraic ℚ secondResponse)
    (first_dimension : Real.log firstResponse / Real.log (first : ℝ) = dimension)
    (second_dimension : Real.log secondResponse / Real.log (second : ℝ) = dimension)
    (irrational : Irrational dimension)
    (incommensurate : ¬ ScaleCommensurate first second) :
    ¬ FourExponentialsReal := by
  intro conjecture
  obtain ⟨i, j, transcendental⟩ := conjecture
    ![Real.log (first : ℝ), Real.log (second : ℝ)] ![dimension, 1]
    (incommensurate_scale_logs_independent first_gt_one second_gt_one incommensurate)
    (irrational_pair_independent dimension irrational)
  have first_log_nonzero : Real.log (first : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast first_gt_one))
  have second_log_nonzero : Real.log (second : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast second_gt_one))
  have first_log_product : Real.log (first : ℝ) * dimension = Real.log firstResponse := by
    have := (div_eq_iff first_log_nonzero).mp first_dimension
    nlinarith
  have second_log_product : Real.log (second : ℝ) * dimension = Real.log secondResponse := by
    have := (div_eq_iff second_log_nonzero).mp second_dimension
    nlinarith
  apply transcendental
  fin_cases i <;> fin_cases j
  · change IsAlgebraic ℚ (Real.exp (Real.log (first : ℝ) * dimension))
    rw [first_log_product, Real.exp_log first_positive]
    exact first_algebraic
  · change IsAlgebraic ℚ (Real.exp (Real.log (first : ℝ) * 1))
    rw [mul_one, Real.exp_log (show 0 < (first : ℝ) by exact_mod_cast (lt_trans Nat.zero_lt_one first_gt_one))]
    simpa using (isAlgebraic_algebraMap (A := ℝ) (first : ℚ))
  · change IsAlgebraic ℚ (Real.exp (Real.log (second : ℝ) * dimension))
    rw [second_log_product, Real.exp_log second_positive]
    exact second_algebraic
  · change IsAlgebraic ℚ (Real.exp (Real.log (second : ℝ) * 1))
    rw [mul_one, Real.exp_log (show 0 < (second : ℝ) by exact_mod_cast (lt_trans Nat.zero_lt_one second_gt_one))]
    simpa using (isAlgebraic_algebraMap (A := ℝ) (second : ℚ))

theorem four_exponentials_commensurability_of_common_irrational_dimension
    (conjecture : FourExponentialsReal)
    {first second : ℕ} {firstResponse secondResponse dimension : ℝ}
    (first_gt_one : 1 < first) (second_gt_one : 1 < second)
    (first_positive : 0 < firstResponse) (second_positive : 0 < secondResponse)
    (first_algebraic : IsAlgebraic ℚ firstResponse)
    (second_algebraic : IsAlgebraic ℚ secondResponse)
    (first_dimension : Real.log firstResponse / Real.log (first : ℝ) = dimension)
    (second_dimension : Real.log secondResponse / Real.log (second : ℝ) = dimension)
    (irrational : Irrational dimension) : ScaleCommensurate first second := by
  by_contra incommensurate
  exact common_irrational_dimension_obstructs_four_exponentials
    first_gt_one second_gt_one first_positive second_positive first_algebraic second_algebraic
    first_dimension second_dimension irrational incommensurate conjecture

end Universality.Section5
