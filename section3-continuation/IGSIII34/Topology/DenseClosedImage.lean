import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.DenseEmbedding

set_option autoImplicit false
namespace IGSIII34.Topology
open Set

theorem range_eq_closure_range_comp_of_dense
    {Index Source Target : Type*} [TopologicalSpace Source] [TopologicalSpace Target]
    (densePoints : Index → Source) (dense : DenseRange densePoints)
    (mapping : Source → Target) (continuous : Continuous mapping)
    (closed : IsClosed (range mapping)) :
    range mapping = closure (range (mapping ∘ densePoints)) := by
  apply Subset.antisymm
  · rintro _ ⟨point, rfl⟩
    have every : ∀ point, mapping point ∈ closure (range (mapping ∘ densePoints)) :=
      isClosed_property dense (isClosed_closure.preimage continuous)
        (fun index => subset_closure ⟨index, rfl⟩)
    exact every point
  · apply closure_minimal _ closed
    rintro _ ⟨index, rfl⟩
    exact ⟨densePoints index, rfl⟩

/-- Two closed continuous images with matching dense labelled points are
the same actual subset of the target. -/
theorem closed_ranges_eq_of_dense_agreement
    {Index First Second Target : Type*} [TopologicalSpace First]
    [TopologicalSpace Second] [TopologicalSpace Target]
    (firstPoints : Index → First) (firstDense : DenseRange firstPoints)
    (secondPoints : Index → Second) (secondDense : DenseRange secondPoints)
    (firstMap : First → Target) (firstContinuous : Continuous firstMap)
    (secondMap : Second → Target) (secondContinuous : Continuous secondMap)
    (firstClosed : IsClosed (range firstMap)) (secondClosed : IsClosed (range secondMap))
    (agreement : ∀ index, firstMap (firstPoints index) = secondMap (secondPoints index)) :
    range firstMap = range secondMap := by
  rw [range_eq_closure_range_comp_of_dense firstPoints firstDense firstMap firstContinuous firstClosed,
    range_eq_closure_range_comp_of_dense secondPoints secondDense secondMap secondContinuous secondClosed]
  congr 2
  exact funext agreement

end IGSIII34.Topology
