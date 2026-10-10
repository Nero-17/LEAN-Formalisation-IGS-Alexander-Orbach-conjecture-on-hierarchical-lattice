import Universality.Matrix.PopulationGrowth

namespace Universality
noncomputable section
open Matrix
set_option maxHeartbeats 0

/-- An inhomogeneous moment recursion grows at most at the forcing rate when
that rate is strictly above the positive eigenvalue of its linear part. -/
theorem matrix_recursion_exponential_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (weight : ι → ℝ) (population : ℕ → ι → ℝ)
    (radius rate forcing : ℝ) (hM : ∀ i j, 0 ≤ M i j) (hw : ∀ i, 0 < weight i)
    (hr : 0 ≤ radius) (hrate : radius < rate) (hf : 0 ≤ forcing)
    (heigen : M *ᵥ weight = radius • weight)
    (hrecursion : ∀ n i, population (n + 1) i ≤
      (M *ᵥ population n) i + forcing * rate ^ n) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ n i, population n i ≤ bound * rate ^ n := by
  classical
  obtain ⟨imin, _, hmin⟩ := Finset.exists_min_image Finset.univ weight Finset.univ_nonempty
  obtain ⟨imax, _, hmax⟩ := Finset.exists_max_image Finset.univ weight Finset.univ_nonempty
  obtain ⟨initialMax, _, hinitialMax⟩ := Finset.exists_max_image Finset.univ
    (fun i => population 0 i / weight i) Finset.univ_nonempty
  have hratePos := lt_of_le_of_lt hr hrate
  have hgap : 0 < (rate - radius) * weight imin := mul_pos (sub_pos.mpr hrate) (hw imin)
  let coefficient := max (max 0 (population 0 initialMax / weight initialMax))
    (forcing / ((rate - radius) * weight imin)) + 1
  have hcoefficient : 0 < coefficient := by
    have : 0 ≤ max (max 0 (population 0 initialMax / weight initialMax))
        (forcing / ((rate - radius) * weight imin)) := (le_max_left _ _).trans (le_max_left _ _)
    dsimp [coefficient]
    linarith
  have hinitial (i : ι) : population 0 i ≤ coefficient * weight i := by
    apply (div_le_iff₀ (hw i)).mp
    calc
      _ ≤ population 0 initialMax / weight initialMax := hinitialMax i (Finset.mem_univ _)
      _ ≤ max 0 (population 0 initialMax / weight initialMax) := le_max_right _ _
      _ ≤ coefficient := by
        have hmax := le_max_left (max 0 (population 0 initialMax / weight initialMax))
          (forcing / ((rate - radius) * weight imin))
        dsimp [coefficient]
        linarith
  have hforcing (i : ι) : forcing ≤ coefficient * (rate - radius) * weight i := by
    have hdivision : forcing / ((rate - radius) * weight imin) ≤ coefficient := by
      dsimp [coefficient]
      linarith [le_max_right (max 0 (population 0 initialMax / weight initialMax))
        (forcing / ((rate - radius) * weight imin))]
    calc
      forcing ≤ coefficient * ((rate - radius) * weight imin) := (div_le_iff₀ hgap).mp hdivision
      _ ≤ coefficient * ((rate - radius) * weight i) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hmin i (Finset.mem_univ _)) (sub_pos.mpr hrate).le) hcoefficient.le
      _ = _ := by ring
  have hbound (n : ℕ) (i : ι) : population n i ≤ coefficient * weight i * rate ^ n := by
    induction n generalizing i with
    | zero => simpa using hinitial i
    | succ n ih =>
      have heigeni := congrFun heigen i
      change (∑ j, M i j * weight j) = radius * weight i at heigeni
      calc
        _ ≤ (M *ᵥ population n) i + forcing * rate ^ n := hrecursion n i
        _ ≤ (∑ j, M i j * (coefficient * weight j * rate ^ n)) + forcing * rate ^ n := by
          apply add_le_add _ le_rfl
          exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (ih j) (hM i j))
        _ = coefficient * (radius * weight i) * rate ^ n + forcing * rate ^ n := by
          rw [← heigeni]
          simp only [Finset.sum_mul, Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro j _
          ring
        _ ≤ coefficient * (radius * weight i) * rate ^ n +
            (coefficient * (rate - radius) * weight i) * rate ^ n :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_right (hforcing i) (pow_pos hratePos n).le)
        _ = coefficient * weight i * rate ^ (n + 1) := by rw [pow_succ]; ring
  refine ⟨coefficient * weight imax, mul_pos hcoefficient (hw imax), ?_⟩
  intro n i
  exact (hbound n i).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hmax i (Finset.mem_univ _)) hcoefficient.le) (pow_pos hratePos n).le)

end
end Universality
