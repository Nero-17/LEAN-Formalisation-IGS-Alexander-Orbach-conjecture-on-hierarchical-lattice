import IGSIII34.Spectral.StrongEigenConvergenceCompletion20261011
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace Filter
open scoped Topology NNReal

variable {Hilbert Index : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  [CompleteSpace Hilbert]

def hilbertBoundedDiagonalCompletion20261011
    (basis : HilbertBasis Index ℝ Hilbert) (coefficient : Index → ℝ)
    (bounded : ∀ index, |coefficient index| ≤ 1) : Hilbert →L[ℝ] Hilbert :=
  basis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((boundedDiagonalL2Completion20261011 coefficient 1 zero_le_one bounded).comp
      basis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem hilbertBoundedDiagonal_norm_le_completion20261011
    (basis : HilbertBasis Index ℝ Hilbert) (coefficient : Index → ℝ)
    (bounded : ∀ index, |coefficient index| ≤ 1) (value : Hilbert) :
    ‖hilbertBoundedDiagonalCompletion20261011 basis coefficient bounded value‖ ≤ ‖value‖ := by
  change ‖basis.repr.symm _‖ ≤ ‖value‖
  rw [basis.repr.symm.norm_map]
  change ‖boundedDiagonalL2ValueCompletion20261011 coefficient 1 zero_le_one bounded (basis.repr value)‖ ≤ ‖value‖
  simpa only [one_mul, basis.repr.norm_map] using boundedDiagonalL2Value_norm_le_completion20261011 coefficient 1 zero_le_one bounded (basis.repr value)

theorem hilbertBoundedDiagonal_basis_completion20261011
    (basis : HilbertBasis Index ℝ Hilbert) (coefficient : Index → ℝ)
    (bounded : ∀ index, |coefficient index| ≤ 1) (index : Index) :
    hilbertBoundedDiagonalCompletion20261011 basis coefficient bounded (basis index) = coefficient index • basis index := by
  classical
  apply basis.repr.injective
  ext other
  change basis.repr (basis.repr.symm _) other = _
  rw [basis.repr.apply_symm_apply, map_smul]
  change coefficient other * basis.repr (basis index) other = coefficient index * basis.repr (basis index) other
  rw [basis.repr_self]
  by_cases same : other = index
  · subst other
    rfl
  · simp [lp.single_apply, same, Ne.symm same]

def eulerSpectralCoefficientCompletion20261011 (time eigenvalue : ℝ) (steps : ℕ) : ℝ :=
  ((1 + time * eigenvalue / (steps : ℝ))⁻¹) ^ steps

theorem eulerSpectralCoefficient_bound_completion20261011
    (time eigenvalue : ℝ) (timeNonnegative : 0 ≤ time) (eigenvalueNonnegative : 0 ≤ eigenvalue) (steps : ℕ) :
    |eulerSpectralCoefficientCompletion20261011 time eigenvalue steps| ≤ 1 := by
  have nonnegative : 0 ≤ time * eigenvalue / (steps : ℝ) := div_nonneg (mul_nonneg timeNonnegative eigenvalueNonnegative) (Nat.cast_nonneg _)
  have baseBound : (1 + time * eigenvalue / (steps : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have baseNonnegative : 0 ≤ (1 + time * eigenvalue / (steps : ℝ))⁻¹ := inv_nonneg.mpr (by linarith)
  rw [eulerSpectralCoefficientCompletion20261011, abs_of_nonneg (pow_nonneg baseNonnegative _)]
  exact pow_le_one₀ baseNonnegative baseBound

theorem eulerSpectralCoefficient_tendsto_completion20261011 (time eigenvalue : ℝ) :
    Tendsto (eulerSpectralCoefficientCompletion20261011 time eigenvalue) atTop (𝓝 (Real.exp (-time * eigenvalue))) := by
  have convergence := (Real.tendsto_one_add_div_pow_exp (time * eigenvalue)).inv₀ (Real.exp_pos _).ne'
  change Tendsto (fun steps : ℕ => ((1 + time * eigenvalue / (steps : ℝ))⁻¹) ^ steps) atTop (𝓝 (Real.exp (-time * eigenvalue)))
  simpa only [inv_pow, Real.exp_neg, neg_mul] using convergence

def eulerSpectralSemigroupCompletion20261011
    (basis : HilbertBasis Index ℝ Hilbert) (eigenvalues : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ eigenvalues index) (time : ℝ≥0) (steps : ℕ) : Hilbert →L[ℝ] Hilbert :=
  hilbertBoundedDiagonalCompletion20261011 basis
    (fun index => eulerSpectralCoefficientCompletion20261011 time (eigenvalues index) steps)
    (fun index => eulerSpectralCoefficient_bound_completion20261011 time (eigenvalues index) time.property (nonnegative index) steps)

theorem eulerSpectralSemigroup_strong_tendsto_completion20261011
    (basis : HilbertBasis Index ℝ Hilbert) (eigenvalues : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ eigenvalues index) (time : ℝ≥0) (value : Hilbert) :
    Tendsto (fun steps => eulerSpectralSemigroupCompletion20261011 basis eigenvalues nonnegative time steps value) atTop
      (𝓝 (spectralL2SemigroupCompletion20261011 basis eigenvalues nonnegative time value)) := by
  apply strong_convergence_of_basis_convergence_completion20261011 basis atTop _ _
    (fun steps value => hilbertBoundedDiagonal_norm_le_completion20261011 _ _ _ value)
    (spectralL2Semigroup_norm_le_completion20261011 basis eigenvalues nonnegative time)
  intro index
  have convergence := (eulerSpectralCoefficient_tendsto_completion20261011 time (eigenvalues index)).smul
    (tendsto_const_nhds (x := basis index))
  simpa only [eulerSpectralSemigroupCompletion20261011, hilbertBoundedDiagonal_basis_completion20261011,
    spectralL2Semigroup_basis_completion20261011] using convergence

end
end IGSIII34.Spectral
