import Mathlib.LinearAlgebra.Eigenspace.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Positive eigenvector certificates

A nonnegative real matrix with a strictly positive eigenvector has spectral
radius equal to the corresponding nonnegative eigenvalue.  This is the precise
finite-dimensional fact needed by the large integer certificates; no general
Perron--Frobenius existence theorem is assumed.
-/

namespace Universality
open Matrix

theorem norm_eigenvalue_le_of_positive_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (weight : ι → ℝ) (radius : ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hw : ∀ i, 0 < weight i)
    (hweight : A *ᵥ weight = radius • weight)
    {μ : ℂ} (hμ : Module.End.HasEigenvalue
      (Matrix.toLin' (A.map Complex.ofReal)) μ) : ‖μ‖ ≤ radius := by
  classical
  haveI : Nonempty ι := hμ.nonempty
  obtain ⟨v, hv, hvne⟩ := hμ.exists_hasEigenvector
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
    (fun j => ‖v j‖ / weight j)
  have hmax (j : ι) : ‖v j‖ / weight j ≤ ‖v i‖ / weight i := by
    exact hi ▸ Finset.le_sup' (fun j => ‖v j‖ / weight j) (Finset.mem_univ j)
  have hvpos : 0 < ‖v i‖ := by
    by_contra hn
    have hzero : ‖v i‖ = 0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    apply hvne
    ext j
    apply norm_eq_zero.mp
    apply le_antisymm
    · have h := hmax j
      rw [hzero, zero_div] at h
      simpa using (div_le_iff₀ (hw j)).mp h
    · exact norm_nonneg _
  have hbound (j : ι) : ‖v j‖ ≤ (‖v i‖ / weight i) * weight j :=
    (div_le_iff₀ (hw j)).mp (hmax j)
  have hμi : μ * v i = ∑ j, (A i j : ℂ) * v j := by
    simpa only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply,
      smul_eq_mul, Matrix.map_apply] using
      (congrFun (Module.End.mem_eigenspace_iff.mp hv) i).symm
  have hwi : ∑ j, A i j * weight j = radius * weight i := by
    simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using
      congrFun hweight i
  have hmain : ‖μ‖ * ‖v i‖ ≤ radius * ‖v i‖ := by
    calc
      ‖μ‖ * ‖v i‖ = ‖μ * v i‖ := (norm_mul _ _).symm
      _ = ‖∑ j, (A i j : ℂ) * v j‖ := by rw [hμi]
      _ ≤ ∑ j, ‖(A i j : ℂ) * v j‖ := norm_sum_le _ _
      _ = ∑ j, A i j * ‖v j‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hA i j)]
      _ ≤ ∑ j, A i j * ((‖v i‖ / weight i) * weight j) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hbound j) (hA i j)
      _ = (‖v i‖ / weight i) * ∑ j, A i j * weight j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = radius * ‖v i‖ := by
        rw [hwi]
        field_simp [ne_of_gt (hw i)]
  exact (mul_le_mul_iff_left₀ hvpos).mp hmain

theorem mem_spectrum_of_positive_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (weight : ι → ℝ) (radius : ℝ)
    (hw : ∀ i, 0 < weight i)
    (hweight : A *ᵥ weight = radius • weight) :
    (radius : ℂ) ∈ spectrum ℂ (A.map Complex.ofReal) := by
  classical
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := fun i => (weight i : ℂ))
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    ext i
    change (∑ j, (A i j : ℂ) * (weight j : ℂ)) = (radius : ℂ) * (weight i : ℂ)
    have h : ∑ j, A i j * weight j = radius * weight i := by
      simpa only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] using
        congrFun hweight i
    exact_mod_cast h
  · intro hzero
    have h := congrFun hzero (Classical.arbitrary ι)
    change (weight (Classical.arbitrary ι) : ℂ) = 0 at h
    apply (ne_of_gt (hw (Classical.arbitrary ι)))
    exact_mod_cast h

/-- A positive-vector certificate determines the genuine complex spectral
radius, including the absolute values of non-real eigenvalues. -/
theorem spectralRadius_eq_of_positive_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (A : Matrix ι ι ℝ) (weight : ι → ℝ) (radius : ℝ)
    (hA : ∀ i j, 0 ≤ A i j) (hw : ∀ i, 0 < weight i)
    (hradius : 0 ≤ radius) (hweight : A *ᵥ weight = radius • weight) :
    spectralRadius ℂ (A.map Complex.ofReal) = ENNReal.ofReal radius := by
  apply le_antisymm
  · apply iSup_le
    intro μ
    apply iSup_le
    intro hμ
    have heigen : Module.End.HasEigenvalue (Matrix.toLin' (A.map Complex.ofReal)) μ := by
      rw [Module.End.hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
      exact hμ
    have hbound := norm_eigenvalue_le_of_positive_eigenvector A weight radius hA hw
      hweight heigen
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal hbound
  · have hmem := mem_spectrum_of_positive_eigenvector A weight radius hw hweight
    apply le_iSup_of_le (radius : ℂ)
    apply le_iSup_of_le hmem
    simp [Real.norm_eq_abs, abs_of_nonneg hradius]

end Universality
