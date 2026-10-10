import Universality.Matrix.PopulationGrowth
import Mathlib.Algebra.Ring.GeomSum

namespace Universality
noncomputable section
open Matrix Filter
open scoped Topology

/-- A strictly positive reward in an affine nonnegative recursion has the
same exponential growth as a positive eigenvector, when the eigenvalue exceeds one. -/
theorem affine_matrix_sum_bounds {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (weight reward : ι → ℝ) (radius : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hw : ∀ i, 0 < weight i)
    (hreward : ∀ i, 0 < reward i) (hr : 1 < radius)
    (heigen : M *ᵥ weight = radius • weight) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ n i, lower * radius ^ n ≤
        ∑ k ∈ Finset.range (n + 1), (M ^ k *ᵥ reward) i ∧
        (∑ k ∈ Finset.range (n + 1), (M ^ k *ᵥ reward) i) ≤ upper * radius ^ n := by
  obtain ⟨imin, _, hmin⟩ := Finset.exists_min_image Finset.univ weight Finset.univ_nonempty
  obtain ⟨imax, _, hmax⟩ := Finset.exists_max_image Finset.univ weight Finset.univ_nonempty
  obtain ⟨jmin, _, hrmin⟩ := Finset.exists_min_image Finset.univ reward Finset.univ_nonempty
  obtain ⟨jmax, _, hrmax⟩ := Finset.exists_max_image Finset.univ reward Finset.univ_nonempty
  have hterm (n : ℕ) (i : ι) :
      (reward jmin * (weight imin / weight imax)) * radius ^ n ≤ (M ^ n *ᵥ reward) i ∧
      (M ^ n *ᵥ reward) i ≤ (reward jmax * (weight imax / weight imin)) * radius ^ n := by
    have hrows := row_sum_power_bounds M weight radius (weight imin) (weight imax)
      hM (lt_trans zero_lt_one hr) (hw _) (hw _)
      (fun j => ⟨hmin j (Finset.mem_univ j), hmax j (Finset.mem_univ j)⟩) heigen n i
    constructor
    · calc
        _ ≤ reward jmin * ∑ j, (M ^ n) i j := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrows.1 (hreward _).le
        _ ≤ _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro j _
          simpa only [mul_comm (reward jmin)] using
            mul_le_mul_of_nonneg_left (hrmin j (Finset.mem_univ j)) (matrix_pow_nonneg M hM n i j)
    · calc
        _ ≤ reward jmax * ∑ j, (M ^ n) i j := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro j _
          simpa only [mul_comm (reward jmax)] using
            mul_le_mul_of_nonneg_left (hrmax j (Finset.mem_univ j)) (matrix_pow_nonneg M hM n i j)
        _ ≤ _ := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hrows.2 (hreward _).le
  have hnonneg (n : ℕ) (i : ι) : 0 ≤ (M ^ n *ᵥ reward) i :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (matrix_pow_nonneg M hM n i j) (hreward j).le)
  refine ⟨reward jmin * (weight imin / weight imax),
    (reward jmax * (weight imax / weight imin)) * radius / (radius - 1),
    mul_pos (hreward _) (div_pos (hw _) (hw _)),
    div_pos (mul_pos (mul_pos (hreward _) (div_pos (hw _) (hw _)))
      (lt_trans zero_lt_one hr)) (sub_pos.mpr hr), ?_⟩
  intro n i
  constructor
  · exact (hterm n i).1.trans (Finset.single_le_sum
      (fun k _ => hnonneg k i) (Finset.mem_range.mpr (Nat.lt_succ_self n)))
  · calc
      _ ≤ ∑ k ∈ Finset.range (n + 1),
          (reward jmax * (weight imax / weight imin)) * radius ^ k :=
        Finset.sum_le_sum (fun k _ => (hterm k i).2)
      _ = (reward jmax * (weight imax / weight imin)) *
          ((radius ^ (n + 1) - 1) / (radius - 1)) := by
        rw [← Finset.mul_sum, (eq_div_iff (sub_pos.mpr hr).ne').mpr (geom_sum_mul radius (n + 1))]
      _ ≤ (reward jmax * (weight imax / weight imin)) *
          (radius ^ (n + 1) / (radius - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_pos (hreward _) (div_pos (hw _) (hw _))).le
        exact div_le_div_of_nonneg_right (by linarith) (sub_pos.mpr hr).le
      _ = _ := by rw [pow_succ]; ring

theorem affine_matrix_sum_logarithmic_growth {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (weight reward : ι → ℝ) (radius : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hw : ∀ i, 0 < weight i)
    (hreward : ∀ i, 0 < reward i) (hr : 1 < radius)
    (heigen : M *ᵥ weight = radius • weight) (i : ι) :
    Tendsto (fun n : ℕ =>
      Real.log (∑ k ∈ Finset.range (n + 1), (M ^ k *ᵥ reward) i) / n)
      atTop (𝓝 (Real.log radius)) := by
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ :=
    affine_matrix_sum_bounds M weight reward radius hM hw hreward hr heigen
  exact logarithmic_growth_of_bounds _ radius lower upper (lt_trans zero_lt_one hr)
    hlower hupper (fun n => hbounds n i)

end
end Universality
