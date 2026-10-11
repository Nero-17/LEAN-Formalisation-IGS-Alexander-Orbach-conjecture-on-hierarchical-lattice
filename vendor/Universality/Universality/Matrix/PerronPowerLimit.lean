import Universality.Matrix.PerronProjection
import Universality.Analysis.NormalizedGeometricSum

namespace Universality
noncomputable section
open Matrix Filter
open scoped Topology BigOperators

theorem positive_matrix_normalized_power_limit (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) (i j : Fin 2) :
    Tendsto (fun n : ℕ => (A ^ n) i j / positiveRoot A ^ n) atTop (𝓝 (perronProjection A i j)) := by
  have hradius := positiveRoot_pos A hA
  have hratio : |secondaryRoot A / positiveRoot A| < 1 := by
    rw [abs_div, abs_of_pos hradius]
    exact (div_lt_one hradius).mpr (secondaryRoot_abs_lt A hA)
  have hdecay := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hratio
  have heq (n : ℕ) : (A ^ n) i j / positiveRoot A ^ n =
      perronProjection A i j + (secondaryRoot A / positiveRoot A) ^ n * (1 - perronProjection A) i j := by
    rw [positive_matrix_power_decomposition A hA]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, div_pow]
    field_simp
  simpa only [heq, zero_mul, add_zero] using
    tendsto_const_nhds.add (hdecay.mul_const ((1 - perronProjection A) i j))

/-- The accumulated mean reward has an explicit Perron-projected limit. -/
theorem positive_matrix_affine_sum_limit (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) (hradius : 1 < positiveRoot A)
    (reward : Fin 2 → ℝ) (i : Fin 2) :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), (A ^ k *ᵥ reward) i) / positiveRoot A ^ n)
      atTop (𝓝 ((positiveRoot A / (positiveRoot A - 1)) * (perronProjection A *ᵥ reward) i)) := by
  have hmain := (normalized_geometric_sum_supercritical (positiveRoot A) hradius).mul_const
    ((perronProjection A *ᵥ reward) i)
  have herror := (normalized_geometric_sum_subcritical (positiveRoot A) (secondaryRoot A) hradius
    (secondaryRoot_abs_lt A hA)).mul_const (((1 - perronProjection A) *ᵥ reward) i)
  have heq (n : ℕ) : (∑ k ∈ Finset.range (n + 1), (A ^ k *ᵥ reward) i) / positiveRoot A ^ n =
      ((∑ k ∈ Finset.range (n + 1), positiveRoot A ^ k) / positiveRoot A ^ n) *
        (perronProjection A *ᵥ reward) i +
      ((∑ k ∈ Finset.range (n + 1), secondaryRoot A ^ k) / positiveRoot A ^ n) *
        ((1 - perronProjection A) *ᵥ reward) i := by
    simp_rw [positive_matrix_power_decomposition A hA, Matrix.add_mulVec, Matrix.smul_mulVec,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, add_div]
    ring
  simpa only [heq, zero_mul, add_zero] using hmain.add herror

theorem perronProjection_mulVec_pos (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) (reward : Fin 2 → ℝ) (hreward : ∀ i, 0 < reward i) :
    ∀ i, 0 < (perronProjection A *ᵥ reward) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact add_pos (mul_pos (perronProjection_pos A hA i 0) (hreward 0))
    (mul_pos (perronProjection_pos A hA i 1) (hreward 1))

theorem positive_eigenvector_proportional (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) (vector : Fin 2 → ℝ)
    (heigen : A *ᵥ vector = positiveRoot A • vector) :
    vector = (vector 0 / A 0 1) • ![A 0 1, positiveRoot A - A 0 0] := by
  have hfirst := congrFun heigen 0
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at hfirst
  funext i
  fin_cases i
  · change vector 0 = vector 0 / A 0 1 * A 0 1
    field_simp [(hA 0 1).ne']
  · change vector 1 = vector 0 / A 0 1 * (positiveRoot A - A 0 0)
    field_simp [(hA 0 1).ne']
    nlinarith

theorem perronProjection_mulVec_proportional (A : Matrix (Fin 2) (Fin 2) ℝ)
    (hA : ∀ i j, 0 < A i j) (reward : Fin 2 → ℝ) :
    perronProjection A *ᵥ reward =
      (((perronProjection A *ᵥ reward) 0) / A 0 1) • ![A 0 1, positiveRoot A - A 0 0] := by
  apply positive_eigenvector_proportional A hA
  rw [Matrix.mulVec_mulVec, mul_perronProjection A hA, Matrix.smul_mulVec]

end
end Universality
