import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Filter

/-- A physical finite family whose overlaps have zero mass has its true
pushforward cell masses identified by the original prefix atoms. The
membership and overlap premises are deterministic geometric facts, proved
for actual continuation cells in the companion modules. -/
theorem pushforward_cell_mass_of_ae_prefix_membership
    {Path Point Index : Type*} [MeasurableSpace Path] [MeasurableSpace Point] [Fintype Index]
    (boundary : Measure Path) (realization : Path → Point) (realizationMeasurable : Measurable realization)
    (index : Path → Index) (weight : Index → ℝ)
    (cell : Index → Set Point) (cellMeasurable : ∀ label, MeasurableSet (cell label))
    (exceptional : Set Point) (exceptionalMeasurable : MeasurableSet exceptional)
    (exceptionalNull : (boundary.map realization) exceptional = 0)
    (atoms : ∀ label, boundary {path | index path = label} = ENNReal.ofReal (weight label))
    (membership : ∀ᵐ path ∂boundary, 0 < weight (index path) ∧ realization path ∈ cell (index path))
    (overlaps : ∀ first last point, 0 < weight first → first ≠ last →
      point ∈ cell first → point ∈ cell last → point ∈ exceptional) :
    (∀ label, (boundary.map realization) (cell label) = ENNReal.ofReal (weight label)) ∧
    (∀ᵐ path ∂boundary, ∀ label, realization path ∈ cell label ↔ index path = label) := by
  have outside : ∀ᵐ path ∂boundary, realization path ∉ exceptional := by
    apply ae_iff.mpr
    simpa only [not_not, Set.preimage, Set.setOf_mem_eq] using
      (Measure.map_apply realizationMeasurable exceptionalMeasurable).symm.trans exceptionalNull
  have identification : ∀ᵐ path ∂boundary, ∀ label, realization path ∈ cell label ↔ index path = label := by
    filter_upwards [membership, outside] with path member outside
    intro label
    constructor
    · intro selected
      by_contra different
      exact outside (overlaps (index path) label (realization path) member.1 different member.2 selected)
    · intro same
      simpa only [← same] using member.2
  refine ⟨?_, identification⟩
  intro label
  rw [Measure.map_apply realizationMeasurable (cellMeasurable label)]
  apply (measure_congr (identification.mono (fun path property => propext (property label)))).trans
  exact atoms label

end
end IGSIII34.Spectral
