import IGSIII4.CoreMinimalCharacterization

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

namespace IGSIII4
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

theorem terminalCoreEdges_substitution_member
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (outerSimple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (innerSimple : Function.Injective (fun edge => s((inner.endpoint edge).1, (inner.endpoint edge).2)))
    (substituteSimple : Function.Injective (fun edge =>
      s(((outer.substitute inner).endpoint edge).1, ((outer.substitute inner).endpoint edge).2)))
    (cells : Fin outerEdges → Configuration innerEdges)
    (crossing : outer.crosses (inner.coarseConfiguration cells) = true)
    (edge : Fin outerEdges) (child : Fin innerEdges) :
    finProdFinEquiv (edge, child) ∈ terminalCoreEdges (outer.substitute inner) (substitutionConfigurationEquiv cells) ↔
      edge ∈ terminalCoreEdges outer (inner.coarseConfiguration cells) ∧
        child ∈ terminalCoreEdges inner (cells edge) := by
  classical
  have fineCrossing : (outer.substitute inner).crosses (substitutionConfigurationEquiv cells) = true := by
    simpa only [outer.substitute_crosses inner] using crossing
  constructor
  · intro membership
    obtain ⟨retained, minimal, subset, opened⟩ :=
      (terminalCoreEdges_member_iff_minimal _ substituteSimple _ fineCrossing _).mp membership
    let retainedCells := substitutionConfigurationEquiv.symm retained
    have retainedConfiguration : substitutionConfigurationEquiv retainedCells = retained :=
      substitutionConfigurationEquiv.apply_symm_apply _
    have retainedMinimal : MinimalCrossingConfiguration (outer.substitute inner)
        (substitutionConfigurationEquiv retainedCells) := by rwa [retainedConfiguration]
    have childOpened : retainedCells edge child = true := by
      rw [← retainedConfiguration] at opened
      simpa only [substitutionConfigurationEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using opened
    have childrenSubset (other : Fin outerEdges) (leaf : Fin innerEdges)
        (retainedHere : retainedCells other leaf = true) : cells other leaf = true := by
      have fineOpened : retained (finProdFinEquiv (other, leaf)) = true := by
        rw [← retainedConfiguration]
        simpa only [substitutionConfigurationEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using retainedHere
      have fineSubset := subset _ fineOpened
      simpa only [substitutionConfigurationEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using fineSubset
    have coarseSubset (other : Fin outerEdges) (retainedHere : inner.coarseConfiguration retainedCells other = true) :
        inner.coarseConfiguration cells other = true :=
      inner.crosses_mono _ _ (childrenSubset other) retainedHere
    have childMinimal := minimal_substitute_children outer inner retainedCells retainedMinimal edge ⟨child, childOpened⟩
    have childCrossing : inner.crosses (cells edge) = true := coarseSubset edge childMinimal.1
    exact ⟨(terminalCoreEdges_member_iff_minimal outer outerSimple _ crossing edge).mpr
      ⟨inner.coarseConfiguration retainedCells, minimal_substitute_coarse outer inner retainedCells retainedMinimal,
        coarseSubset, childMinimal.1⟩,
      (terminalCoreEdges_member_iff_minimal inner innerSimple _ childCrossing child).mpr
        ⟨retainedCells edge, childMinimal, childrenSubset edge, childOpened⟩⟩
  · rintro ⟨parentMembership, childMembership⟩
    have childCrossing : inner.crosses (cells edge) = true :=
      (terminalCoreEdges_open_active outer outerSimple _ parentMembership).1
    obtain ⟨retainedParent, parentMinimal, parentSubset, parentOpened⟩ :=
      (terminalCoreEdges_member_iff_minimal outer outerSimple _ crossing edge).mp parentMembership
    obtain ⟨retainedChild, childMinimal, childSubset, childOpened⟩ :=
      (terminalCoreEdges_member_iff_minimal inner innerSimple _ childCrossing child).mp childMembership
    let defaultPath (other : Fin outerEdges) := (edgePathFamily inner (cells other)).nonempty.choose
    have defaultMembership (other : Fin outerEdges) :
        defaultPath other ∈ (edgePathFamily inner (cells other)).paths :=
      (edgePathFamily inner (cells other)).nonempty.choose_spec
    let selectedCells (other : Fin outerEdges) : Configuration innerEdges :=
      if retainedParent other = true then
        if other = edge then retainedChild else configurationOfPath (defaultPath other)
      else fun _ => false
    have selectedChildMinimal (other : Fin outerEdges) (retainedHere : retainedParent other = true) :
        MinimalCrossingConfiguration inner (selectedCells other) := by
      by_cases same : other = edge
      · subst other
        simpa only [selectedCells, if_pos retainedHere, if_pos rfl, ite_true] using childMinimal
      · simp only [selectedCells, if_pos retainedHere, if_neg same]
        exact edgePathFamily_member_minimal inner innerSimple _ (parentSubset other retainedHere) (defaultMembership other)
    have selectedCoarse : inner.coarseConfiguration selectedCells = retainedParent := by
      funext other
      cases retainedHere : retainedParent other with
      | true => exact (selectedChildMinimal other retainedHere).1
      | false => simp [FiniteNetwork.coarseConfiguration, selectedCells, retainedHere, inner.crosses_all_closed]
    have selectedMinimal : MinimalCrossingConfiguration (outer.substitute inner)
        (substitutionConfigurationEquiv selectedCells) := by
      apply minimal_substitute_of_children outer inner selectedCells
      · rwa [selectedCoarse]
      · intro other nonempty
        cases retainedHere : retainedParent other with
        | true => exact selectedChildMinimal other retainedHere
        | false =>
            obtain ⟨leaf, impossible⟩ := nonempty
            simp [selectedCells, retainedHere] at impossible
    have selectedSubset (leaf : Fin (outerEdges * innerEdges))
        (retainedHere : substitutionConfigurationEquiv selectedCells leaf = true) :
        substitutionConfigurationEquiv cells leaf = true := by
      obtain ⟨⟨other, descendant⟩, rfl⟩ := finProdFinEquiv.surjective leaf
      simp only [substitutionConfigurationEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] at retainedHere ⊢
      by_cases parentOpen : retainedParent other = true
      · by_cases same : other = edge
        · subst other
          simp only [selectedCells, if_pos parentOpen, if_pos rfl, ite_true] at retainedHere
          exact childSubset descendant retainedHere
        · simp only [selectedCells, if_pos parentOpen, if_neg same, configurationOfPath] at retainedHere
          exact edgePathFamily_used_edge inner innerSimple _ (defaultMembership other) (of_decide_eq_true retainedHere)
      · simp [selectedCells, parentOpen] at retainedHere
    apply (terminalCoreEdges_member_iff_minimal _ substituteSimple _ fineCrossing _).mpr
    refine ⟨substitutionConfigurationEquiv selectedCells, selectedMinimal, selectedSubset, ?_⟩
    simpa only [substitutionConfigurationEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply,
      selectedCells, if_pos parentOpened, if_pos rfl, ite_true] using childOpened

end
end IGSIII4
