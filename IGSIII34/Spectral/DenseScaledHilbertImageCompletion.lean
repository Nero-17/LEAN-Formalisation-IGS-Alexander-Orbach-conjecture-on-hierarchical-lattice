import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.LinearAlgebra.Span.Basic

set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open scoped Topology
variable {Index Energy Target : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup Target] [NormedSpace ℝ Target]

theorem dense_span_scaled_hilbert_image_completion
    (basis : HilbertBasis Index ℝ Energy) (embedding : Energy →L[ℝ] Target)
    (embeddingDense : DenseRange embedding) (scale : Index → ℝ)
    (scaleNonzero : ∀ index, scale index ≠ 0) :
    Dense ((Submodule.span ℝ (Set.range (fun index => (scale index)⁻¹ • embedding (basis index)))) : Set Target) := by
  have mappedDense := embeddingDense.topologicalClosure_map_submodule basis.dense_span
  have inclusion : (Submodule.span ℝ (Set.range basis)).map embedding.toLinearMap ≤
      Submodule.span ℝ (Set.range (fun index => (scale index)⁻¹ • embedding (basis index))) := by
    apply (Submodule.map_span_le embedding.toLinearMap (Set.range basis) _).mpr
    rintro _ ⟨index, rfl⟩
    have scaledMember := (Submodule.span ℝ (Set.range
      (fun index => (scale index)⁻¹ • embedding (basis index)))).smul_mem (scale index)
        (Submodule.subset_span (Set.mem_range_self index))
    simpa only [smul_smul, mul_inv_cancel₀ (scaleNonzero index), one_smul, ContinuousLinearMap.coe_coe] using scaledMember
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  rw [← mappedDense]
  exact Submodule.topologicalClosure_mono inclusion

end
end IGSIII34.Spectral
