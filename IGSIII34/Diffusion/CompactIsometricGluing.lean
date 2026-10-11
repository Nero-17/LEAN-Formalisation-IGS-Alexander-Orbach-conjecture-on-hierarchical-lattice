import Mathlib.Topology.MetricSpace.Gluing
import Mathlib.Topology.MetricSpace.GromovHausdorff

set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open Set

variable {First Middle Last : Type*}
  [MetricSpace First] [CompactSpace First]
  [MetricSpace Middle] [Nonempty Middle]
  [MetricSpace Last] [CompactSpace Last]
  {firstPlacement : Middle → First} {lastPlacement : Middle → Last}

theorem compactIsometricGluing_range_union
    (firstIsometry : Isometry firstPlacement) (lastIsometry : Isometry lastPlacement) :
    range (Metric.toGlueL firstIsometry lastIsometry) ∪
      range (Metric.toGlueR firstIsometry lastIsometry) = univ := by
  apply eq_univ_of_forall
  intro point
  induction point using Quotient.inductionOn with
  | h point =>
    cases point with
    | inl point => exact Or.inl ⟨point, rfl⟩
    | inr point => exact Or.inr ⟨point, rfl⟩

/-- Gluing two compact metric spaces along a common nonempty isometric
subspace gives a compact metric space, including when the gluing identifies
additional zero-distance representatives. -/
instance compactIsometricGluing_compactSpace
    (firstIsometry : Isometry firstPlacement) (lastIsometry : Isometry lastPlacement) :
    CompactSpace (Metric.GlueSpace firstIsometry lastIsometry) := by
  apply CompactSpace.mk
  rw [← compactIsometricGluing_range_union firstIsometry lastIsometry]
  exact (isCompact_range (Metric.toGlueL_isometry firstIsometry lastIsometry).continuous).union
    (isCompact_range (Metric.toGlueR_isometry firstIsometry lastIsometry).continuous)

end
end IGSIII34.Diffusion
