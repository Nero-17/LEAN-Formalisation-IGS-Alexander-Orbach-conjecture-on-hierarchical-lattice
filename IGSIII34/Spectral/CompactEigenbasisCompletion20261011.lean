import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! A genuine Hilbert eigenbasis is obtained from the compact self-adjoint
spectral theorem. It is constructed from the eigenspaces and is not an
additional spectral-data assumption. Countable ordering is a later step. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open Module Module.End InnerProductSpace
open scoped Topology
universe u

theorem exists_compact_selfadjoint_Hilbert_eigenbasis_completion20261011
    {Hilbert : Type u} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    [CompleteSpace Hilbert] (operator : Hilbert →L[ℝ] Hilbert)
    (compact : IsCompactOperator operator) (symmetric : operator.toLinearMap.IsSymmetric) :
    ∃ Index : Type u, ∃ basis : HilbertBasis Index ℝ Hilbert,
      ∃ eigenvalue : Index → ℝ, ∀ index, operator (basis index) = eigenvalue index • basis index := by
  classical
  have bases (value : ℝ) :
      ∃ indices : Set (eigenspace operator.toLinearMap value),
        Nonempty (HilbertBasis indices ℝ (eigenspace operator.toLinearMap value)) := by
    letI : CompleteSpace (eigenspace operator.toLinearMap value) :=
      (ContinuousLinearMap.isClosed_eigenspace operator value).completeSpace_coe
    obtain ⟨indices, basis, _⟩ := exists_hilbertBasis ℝ (eigenspace operator.toLinearMap value)
    exact ⟨indices, ⟨basis⟩⟩
  choose indices basisExists using bases
  let basis (value : ℝ) : HilbertBasis (indices value) ℝ (eigenspace operator.toLinearMap value) :=
    Classical.choice (basisExists value)
  let eigenvectors : (Σ value : ℝ, indices value) → Hilbert :=
    fun index => (basis index.1 index.2).val
  have orthonormal : Orthonormal ℝ eigenvectors :=
    symmetric.orthogonalFamily_eigenspaces.orthonormal_sigma_orthonormal
      (fun value => (basis value).orthonormal)
  have trivial : (Submodule.span ℝ (Set.range eigenvectors))ᗮ = ⊥ := by
    apply eq_bot_iff.mpr
    intro point orthogonal
    have orthogonalEigenspaces : point ∈ (⨆ value : ℝ, eigenspace operator.toLinearMap value)ᗮ := by
      rw [← Submodule.iInf_orthogonal]
      simp only [Submodule.mem_iInf]
      intro value
      rw [Submodule.mem_orthogonal']
      intro vector member
      let evaluation : eigenspace operator.toLinearMap value →L[ℝ] ℝ :=
        (innerSL ℝ point).comp (eigenspace operator.toLinearMap value).subtypeL
      have vanishing : Submodule.span ℝ (Set.range (basis value)) ≤ evaluation.ker := by
        apply Submodule.span_le.mpr
        rintro _ ⟨index, rfl⟩
        change inner ℝ point (basis value index).val = 0
        rw [real_inner_comm]
        exact Submodule.inner_right_of_mem_orthogonal
          (Submodule.subset_span (Set.mem_range.mpr ⟨⟨value, index⟩, rfl⟩)) orthogonal
      have total := (Submodule.span ℝ (Set.range (basis value))).topologicalClosure_minimal
        vanishing evaluation.isClosed_ker
      rw [(basis value).dense_span] at total
      exact total (show (⟨vector, member⟩ : eigenspace operator.toLinearMap value) ∈ ⊤ by trivial)
    rw [ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot compact symmetric] at orthogonalEigenspaces
    exact orthogonalEigenspaces
  let totalBasis := HilbertBasis.mkOfOrthogonalEqBot orthonormal trivial
  refine ⟨(Σ value : ℝ, indices value), totalBasis, (fun index => index.1), ?_⟩
  intro index
  have equality : totalBasis index = eigenvectors index :=
    congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot orthonormal trivial) index
  rw [equality]
  exact (mem_eigenspace_iff.mp (basis index.1 index.2).property)

end
end IGSIII34.Spectral
