import IGSIII34.Spectral.Collars.CellMassIdentification

set_option autoImplicit false

namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory

/-- The unique containing cell is a property of the physical point,
obtained from the original boundary realization and finite measurable
cells. No measurable choice of boundary path is needed. -/
theorem pushforward_ae_unique_containing_cell
    {Path Point Index : Type*} [MeasurableSpace Path] [MeasurableSpace Point] [Fintype Index]
    (boundary : Measure Path) (realization : Path → Point)
    (realizationMeasurable : Measurable realization) (index : Path → Index)
    (cell : Index → Set Point) (cellMeasurable : ∀ label, MeasurableSet (cell label))
    (identification : ∀ᵐ path ∂boundary, ∀ label,
      realization path ∈ cell label ↔ index path = label) :
    ∀ᵐ point ∂boundary.map realization, ∃ label, ∀ other,
      point ∈ cell other ↔ other = label := by
  have measurable : MeasurableSet {point | ∃ label, ∀ other,
      point ∈ cell other ↔ other = label} := by
    apply Measurable.setOf
    apply Measurable.exists
    intro label
    apply Measurable.forall
    intro other
    exact (cellMeasurable other).mem.iff measurable_const
  apply (ae_map_iff realizationMeasurable.aemeasurable measurable).mpr
  filter_upwards [identification] with path property
  refine ⟨index path, ?_⟩
  intro other
  exact (property other).trans eq_comm

end
end IGSIII34.Spectral
