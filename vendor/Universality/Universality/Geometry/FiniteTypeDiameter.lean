import Universality.Geometry.ContractiveRealisation
import Mathlib.Data.Finset.Lattice.Fold

namespace Universality.Geometry
noncomputable section
open Set Metric

variable {Colour : Type*} [Fintype Colour] [Nonempty Colour]
variable (Space : Colour → Type*) [∀ i, MetricSpace (Space i)] [∀ i, CompactSpace (Space i)]

/-- The exact common diameter bound appearing in the manuscript. -/
def maximumTypeDiameter : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => diam (univ : Set (Space i)))

omit [∀ i, CompactSpace (Space i)] in
theorem type_diameter_le_maximum (i : Colour) :
    diam (univ : Set (Space i)) ≤ maximumTypeDiameter Space :=
  Finset.le_sup' (f := fun i => diam (univ : Set (Space i))) (Finset.mem_univ i)

omit [∀ i, CompactSpace (Space i)] in
theorem maximumTypeDiameter_nonneg : 0 ≤ maximumTypeDiameter Space := by
  obtain ⟨i⟩ := ‹Nonempty Colour›
  exact diam_nonneg.trans (type_diameter_le_maximum Space i)

theorem type_dist_le_maximum (i : Colour) (x y : Space i) :
    dist x y ≤ maximumTypeDiameter Space :=
  (dist_le_diam_of_mem isCompact_univ.isBounded (mem_univ x) (mem_univ y)).trans
    (type_diameter_le_maximum Space i)

end
end Universality.Geometry
