import IGSIII34.Spectral.CoerciveFormHilbertCompletion20261011
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! The actual energy-normalized basis is constructed from the L2
resolvent eigenbasis and its variational solution. Completeness follows
from injectivity of the actual embedding, not an assumed energy basis. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace
open scoped Topology

variable {Energy L2 Index : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]

def normalisedResolventEigenvectorsCompletion20261011
    (solution : L2 →L[ℝ] Energy) (basis : HilbertBasis Index ℝ L2)
    (eigenvalues : Index → ℝ) : Index → Energy :=
  fun index => (Real.sqrt (eigenvalues index))⁻¹ • solution (basis index)

theorem normalisedResolventEigenvectors_orthonormal_completion20261011
    (embedding : Energy →L[ℝ] L2) (solution : L2 →L[ℝ] Energy)
    (variational : ∀ forcing test, inner ℝ (solution forcing) test = inner ℝ forcing (embedding test))
    (basis : HilbertBasis Index ℝ L2) (eigenvalues : Index → ℝ)
    (positive : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, embedding (solution (basis index)) = eigenvalues index • basis index) :
    Orthonormal ℝ (normalisedResolventEigenvectorsCompletion20261011 solution basis eigenvalues) := by
  classical
  apply orthonormal_iff_ite.mpr
  intro first second
  simp only [normalisedResolventEigenvectorsCompletion20261011, inner_smul_left,
    inner_smul_right, variational, eigenvectors, inner_smul_right, starRingEnd_apply, star_trivial]
  by_cases same : first = second
  · subst second
    rw [real_inner_self_eq_norm_sq, basis.orthonormal.norm_eq_one]
    simp only [↓reduceIte, one_pow, mul_one]
    have nonzero := (Real.sqrt_pos.mpr (positive first)).ne'
    have square := Real.sq_sqrt (positive first).le
    field_simp [nonzero]
    nlinarith
  · rw [basis.orthonormal.inner_eq_zero same]
    simp only [same, ↓reduceIte, mul_zero]

theorem normalisedResolventEigenvectors_total_completion20261011
    (embedding : Energy →L[ℝ] L2) (injective : Function.Injective embedding)
    (solution : L2 →L[ℝ] Energy)
    (variational : ∀ forcing test, inner ℝ (solution forcing) test = inner ℝ forcing (embedding test))
    (basis : HilbertBasis Index ℝ L2) (eigenvalues : Index → ℝ)
    (positive : ∀ index, 0 < eigenvalues index) :
    (Submodule.span ℝ (Set.range
      (normalisedResolventEigenvectorsCompletion20261011 solution basis eigenvalues)))ᗮ = ⊥ := by
  apply eq_bot_iff.mpr
  intro potential orthogonal
  have coefficients (index : Index) : inner ℝ (basis index) (embedding potential) = 0 := by
    have vanishing := Submodule.inner_right_of_mem_orthogonal
      (Submodule.subset_span (Set.mem_range_self index)) orthogonal
    simp only [normalisedResolventEigenvectorsCompletion20261011, inner_smul_left, variational] at vanishing
    exact (mul_eq_zero.mp vanishing).resolve_left (inv_ne_zero (Real.sqrt_pos.mpr (positive index)).ne')
  have imageZero : embedding potential = 0 := by
    apply basis.repr.injective
    ext index
    simpa [basis.repr_apply_apply] using coefficients index
  have potentialZero : potential = 0 := injective (imageZero.trans embedding.map_zero.symm)
  exact potentialZero

def resolventEnergyHilbertBasisCompletion20261011
    (embedding : Energy →L[ℝ] L2) (injective : Function.Injective embedding)
    (solution : L2 →L[ℝ] Energy)
    (variational : ∀ forcing test, inner ℝ (solution forcing) test = inner ℝ forcing (embedding test))
    (basis : HilbertBasis Index ℝ L2) (eigenvalues : Index → ℝ)
    (positive : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, embedding (solution (basis index)) = eigenvalues index • basis index) :
    HilbertBasis Index ℝ Energy :=
  HilbertBasis.mkOfOrthogonalEqBot
    (normalisedResolventEigenvectors_orthonormal_completion20261011 embedding solution variational
      basis eigenvalues positive eigenvectors)
    (normalisedResolventEigenvectors_total_completion20261011 embedding injective solution variational
      basis eigenvalues positive)

end
end IGSIII34.Spectral
