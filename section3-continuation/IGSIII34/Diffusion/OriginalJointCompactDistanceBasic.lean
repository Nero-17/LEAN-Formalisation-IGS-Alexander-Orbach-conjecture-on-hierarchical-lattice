import IGSIII34.Diffusion.OriginalJointCompactCoupling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Set TopologicalSpace MeasureTheory Metric
open scoped BigOperators ENNReal

theorem OriginalJointCompactCoupling.exists
    (first last : OriginalJointCompactRepresentative) :
    Nonempty (OriginalJointCompactCoupling first last) := by
  letI : MetricSpace (first.carrier ⊕ last.carrier) := metricSpaceSum
  let embedding := (kuratowskiEmbedding.isometry
    (first.carrier ⊕ last.carrier)).isometryEquivOnRange
  exact ⟨{
    ambient := NonemptyCompacts.kuratowskiEmbedding (first.carrier ⊕ last.carrier)
    firstPlacement := embedding ∘ Sum.inl
    firstIsometry := embedding.isometry.comp isometry_inl
    lastPlacement := embedding ∘ Sum.inr
    lastIsometry := embedding.isometry.comp isometry_inr }⟩

theorem OriginalJointCompactCoupling.cost_reflexive
    (representative : OriginalJointCompactRepresentative) :
    (OriginalJointCompactCoupling.reflexive representative).cost = 0 := by
  simp [OriginalJointCompactCoupling.cost, OriginalJointCompactCoupling.reflexive,
    jointMeasuredMarkedStateCost, levyProkhorovDist_self]

theorem OriginalJointCompactCoupling.cost_reverse
    {first last : OriginalJointCompactRepresentative}
    (coupling : OriginalJointCompactCoupling first last) : coupling.reverse.cost = coupling.cost := by
  simp only [OriginalJointCompactCoupling.cost, OriginalJointCompactCoupling.reverse,
    jointMeasuredMarkedStateCost, dist_comm, levyProkhorovDist_comm]

/-- The common-embedding joint distance uses the ORIGINAL carrier metric,
two physical masses and planted marks, and whole integer-horizon J1.
Its subsequent usual-local interpretation is only at continuous limits. -/
def originalJointCompactDistance
    (first last : OriginalJointCompactRepresentative) : ℝ :=
  sInf (range (fun coupling : OriginalJointCompactCoupling first last => coupling.cost))

theorem originalJointCompactDistance_bddBelow
    (first last : OriginalJointCompactRepresentative) :
    BddBelow (range (fun coupling : OriginalJointCompactCoupling first last => coupling.cost)) :=
  ⟨0, by rintro _ ⟨coupling, rfl⟩; exact coupling.cost_nonnegative⟩

theorem originalJointCompactDistance_range_nonempty
    (first last : OriginalJointCompactRepresentative) :
    (range (fun coupling : OriginalJointCompactCoupling first last => coupling.cost)).Nonempty := by
  obtain ⟨coupling⟩ := OriginalJointCompactCoupling.exists first last
  exact ⟨coupling.cost, ⟨coupling, rfl⟩⟩

theorem originalJointCompactDistance_nonnegative
    (first last : OriginalJointCompactRepresentative) :
    0 ≤ originalJointCompactDistance first last := by
  apply le_csInf (originalJointCompactDistance_range_nonempty first last)
  rintro _ ⟨coupling, rfl⟩
  exact coupling.cost_nonnegative

theorem originalJointCompactDistance_le_cost
    {first last : OriginalJointCompactRepresentative}
    (coupling : OriginalJointCompactCoupling first last) :
    originalJointCompactDistance first last ≤ coupling.cost :=
  csInf_le (originalJointCompactDistance_bddBelow first last) ⟨coupling, rfl⟩

theorem originalJointCompactDistance_self
    (representative : OriginalJointCompactRepresentative) :
    originalJointCompactDistance representative representative = 0 := by
  apply le_antisymm
  · exact (originalJointCompactDistance_le_cost
      (OriginalJointCompactCoupling.reflexive representative)).trans_eq
      (OriginalJointCompactCoupling.cost_reflexive representative)
  · exact originalJointCompactDistance_nonnegative _ _

theorem originalJointCompactDistance_comm
    (first last : OriginalJointCompactRepresentative) :
    originalJointCompactDistance first last = originalJointCompactDistance last first := by
  have bound (first last : OriginalJointCompactRepresentative) :
      originalJointCompactDistance first last ≤ originalJointCompactDistance last first := by
    apply le_csInf (originalJointCompactDistance_range_nonempty last first)
    rintro _ ⟨coupling, rfl⟩
    exact (originalJointCompactDistance_le_cost coupling.reverse).trans_eq coupling.cost_reverse
  exact (bound first last).antisymm (bound last first)

theorem originalJointCompactDistance_lt_iff
    (first last : OriginalJointCompactRepresentative) (tolerance : ℝ) :
    originalJointCompactDistance first last < tolerance ↔
      ∃ coupling : OriginalJointCompactCoupling first last, coupling.cost < tolerance := by
  rw [originalJointCompactDistance,
    csInf_lt_iff (originalJointCompactDistance_bddBelow first last)
      (originalJointCompactDistance_range_nonempty first last)]
  constructor
  · rintro ⟨_, ⟨coupling, rfl⟩, bound⟩
    exact ⟨coupling, bound⟩
  · rintro ⟨coupling, bound⟩
    exact ⟨coupling.cost, ⟨coupling, rfl⟩, bound⟩

end
end IGSIII34.Diffusion
