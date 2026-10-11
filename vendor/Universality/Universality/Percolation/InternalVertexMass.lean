import Universality.Percolation.OrientedStates

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

/-- Internal vertices in the selected terminal clusters, counted once and
excluding both planting vertices. This is the mass used in Section 3. -/
def internalSelectedMass (R : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (ω : Configuration edges) : ℕ :=
  ∑ v : R.InteriorVertex, if R.selectedActive sourceSelected targetSelected ω v.val then 1 else 0

def internalStateMass (R : FiniteNetwork vertices edges)
    (parent : OrientedState) (ω : Configuration edges) : ℕ :=
  R.internalSelectedMass parent.sourceSelected parent.targetSelected ω

theorem internalSelectedMass_le (R : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (ω : Configuration edges) :
    R.internalSelectedMass sourceSelected targetSelected ω ≤ Fintype.card R.InteriorVertex := by
  unfold internalSelectedMass
  calc
    _ ≤ ∑ _ : R.InteriorVertex, 1 := by
      apply Finset.sum_le_sum
      intro v _
      split <;> omega
    _ = _ := by simp

theorem internalStateMass_inactive (R : FiniteNetwork vertices edges) (ω : Configuration edges) :
    R.internalStateMass .inactive ω = 0 := by
  simp [internalStateMass, internalSelectedMass, OrientedState.sourceSelected,
    OrientedState.targetSelected, selectedActive]

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- The internal vertices of a glued network are exactly the old internal
vertices together with the disjoint internal vertices of every child cell. -/
def substitutionInteriorEquiv :
    R.InteriorVertex ⊕ (Fin outerEdges × S.InteriorVertex) ≃ (R.substitute S).InteriorVertex :=
  Equiv.ofBijective
    (fun x => match x with
      | .inl v => ⟨Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl v.val), by
          constructor
          · intro h
            exact v.property.1 (Sum.inl.inj ((Fintype.equivFin (R.SubstitutionVertex S)).injective h))
          · intro h
            exact v.property.2 (Sum.inl.inj ((Fintype.equivFin (R.SubstitutionVertex S)).injective h))⟩
      | .inr child => ⟨Fintype.equivFin (R.SubstitutionVertex S) (Sum.inr child), by
          constructor <;> intro h <;>
            have h' := (Fintype.equivFin (R.SubstitutionVertex S)).injective h <;> cases h'⟩)
    ⟨by
      intro first second h
      cases first with
      | inl v =>
        cases second with
        | inl w =>
          have hval := (Fintype.equivFin (R.SubstitutionVertex S)).injective (congrArg Subtype.val h)
          exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj hval))
        | inr child =>
          have hval := (Fintype.equivFin (R.SubstitutionVertex S)).injective (congrArg Subtype.val h)
          cases hval
      | inr child =>
        cases second with
        | inl v =>
          have hval := (Fintype.equivFin (R.SubstitutionVertex S)).injective (congrArg Subtype.val h)
          cases hval
        | inr other =>
          have hval := (Fintype.equivFin (R.SubstitutionVertex S)).injective (congrArg Subtype.val h)
          exact congrArg Sum.inr (Sum.inr.inj hval), by
      rintro ⟨vertex, hvertex⟩
      cases h : (Fintype.equivFin (R.SubstitutionVertex S)).symm vertex with
      | inl v =>
        have heq : Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl v) = vertex :=
          (congrArg (Fintype.equivFin (R.SubstitutionVertex S)) h).symm.trans
            ((Fintype.equivFin (R.SubstitutionVertex S)).apply_symm_apply vertex)
        have hv : v ≠ R.source ∧ v ≠ R.target := by
          constructor
          · intro hsource
            apply hvertex.1
            subst v
            exact heq.symm
          · intro htarget
            apply hvertex.2
            subst v
            exact heq.symm
        exact ⟨Sum.inl ⟨v, hv⟩, Subtype.ext heq⟩
      | inr child =>
        refine ⟨Sum.inr child, Subtype.ext ?_⟩
        exact (congrArg (Fintype.equivFin (R.SubstitutionVertex S)) h).symm.trans
          ((Fintype.equivFin (R.SubstitutionVertex S)).apply_symm_apply vertex)⟩

theorem selectedActive_substitute_coarse (sourceSelected targetSelected : Bool)
    (ω : Fin outerEdges → Configuration innerEdges) (v : Fin outerVertices) :
    (R.substitute S).selectedActive sourceSelected targetSelected
      (substitutionConfigurationEquiv ω) (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl v)) =
      R.selectedActive sourceSelected targetSelected (S.coarseConfiguration ω) v := by
  apply Bool.eq_iff_iff.mpr
  simp only [selectedActive, Bool.or_eq_true, Bool.and_eq_true,
    SimpleGraph.reachableDecide_eq_true]
  change ((sourceSelected = true ∧
      ((R.substitute S).openGraph (substitutionConfigurationEquiv ω)).Reachable
        (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl R.source)) (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl v))) ∨
    (targetSelected = true ∧
      ((R.substitute S).openGraph (substitutionConfigurationEquiv ω)).Reachable
        (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl R.target)) (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl v)))) ↔ _
  simp only [R.substitute_reachable_iff S, R.substitutedReachable_iff S]

/-- Exact, pathwise, reward-plus-children recursion. No independence is
assumed here; conditional independence is supplied by the joint-law theorem. -/
theorem internalSelectedMass_substitute (sourceSelected targetSelected : Bool)
    (ω : Fin outerEdges → Configuration innerEdges) :
    (R.substitute S).internalSelectedMass sourceSelected targetSelected
      (substitutionConfigurationEquiv ω) =
      R.internalSelectedMass sourceSelected targetSelected (S.coarseConfiguration ω) +
        ∑ e, S.internalStateMass
          (R.orientedChildState sourceSelected targetSelected (S.coarseConfiguration ω) e) (ω e) := by
  unfold internalSelectedMass
  rw [← (R.substitutionInteriorEquiv S).sum_comp]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  congr 1
  · apply Finset.sum_congr rfl
    intro v _
    change (if (R.substitute S).selectedActive sourceSelected targetSelected
      (substitutionConfigurationEquiv ω) (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl v.val)) then 1 else 0) = _
    rw [R.selectedActive_substitute_coarse S]
  · apply Finset.sum_congr rfl
    intro e _
    unfold internalStateMass internalSelectedMass
    apply Finset.sum_congr rfl
    intro v _
    have hcell : R.cellVertex S e v.val = Sum.inr (e, v) := by
      simp [cellVertex, v.property.1, v.property.2]
    change (if (R.substitute S).selectedActive sourceSelected targetSelected
      (substitutionConfigurationEquiv ω) (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inr (e, v))) then 1 else 0) = _
    rw [← hcell, R.selectedActive_substitute_cell S]
    simp only [orientedChildState, orientedStateOf_sourceSelected, orientedStateOf_targetSelected]

end
end Universality.FiniteNetwork
