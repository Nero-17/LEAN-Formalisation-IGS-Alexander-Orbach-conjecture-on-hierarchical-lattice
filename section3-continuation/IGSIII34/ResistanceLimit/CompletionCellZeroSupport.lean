import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false
namespace IGSIII34.ResistanceLimit

/-- Zero extension on a dense retained skeleton vanishes everywhere outside
the closed component. This also covers all completion points. -/
theorem continuous_zero_outside_closed_cell_of_dense
    {Skeleton Carrier : Type*} [TopologicalSpace Carrier]
    (born : Skeleton → Carrier) (dense : DenseRange born)
    (cell : Set Carrier) (closed : IsClosed cell) (potential : C(Carrier, ℝ))
    (zero : ∀ point, born point ∉ cell → potential (born point) = 0) :
    ∀ point, point ∉ cell → potential point = 0 := by
  have closedUnion : IsClosed (cell ∪ {point | potential point = 0}) :=
    closed.union (isClosed_eq potential.continuous continuous_const)
  have included : Set.range born ⊆ cell ∪ {point | potential point = 0} := by
    rintro point ⟨vertex, rfl⟩
    by_cases belongs : born vertex ∈ cell
    · exact Or.inl belongs
    · exact Or.inr (zero vertex belongs)
  have everywhere := closedUnion.closure_subset_iff.mpr included
  rw [dense.closure_range] at everywhere
  intro point outside
  exact (everywhere (Set.mem_univ point)).resolve_left outside

end IGSIII34.ResistanceLimit
