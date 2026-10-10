import IGSIII.Chemical.SubstitutionPaths.MinimalPaths

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork
open scoped BigOperators

theorem openEdges_substitution_pathCost {outerEdges innerEdges : ℕ}
    (cells : Fin outerEdges → Configuration innerEdges) (cost : Fin (outerEdges * innerEdges) → ℝ) :
    PathFamily.pathCost (openEdges (substitutionConfigurationEquiv cells)) cost =
      ∑ edge, PathFamily.pathCost (openEdges (cells edge)) (fun child => cost (finProdFinEquiv (edge, child))) := by
  classical
  simp only [PathFamily.pathCost, openEdges, Finset.sum_filter]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp only [substitutionConfigurationEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply]

theorem minimal_substitute_child_closed
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (cells : Fin outerEdges → Configuration innerEdges)
    (minimal : MinimalCrossingConfiguration (outer.substitute inner) (substitutionConfigurationEquiv cells))
    (edge : Fin outerEdges) (closed : inner.crosses (cells edge) ≠ true) :
    cells edge = fun _ => false := by
  funext child
  cases retained : cells edge child with
  | false => rfl
  | true => exact False.elim (closed (minimal_substitute_children outer inner cells minimal edge ⟨child, retained⟩).1)

theorem substitute_edgePathFamily_shortest
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (outerSimple : Function.Injective (fun edge => s((outer.endpoint edge).1, (outer.endpoint edge).2)))
    (innerSimple : Function.Injective (fun edge => s((inner.endpoint edge).1, (inner.endpoint edge).2)))
    (substituteSimple : Function.Injective (fun edge =>
      s(((outer.substitute inner).endpoint edge).1, ((outer.substitute inner).endpoint edge).2)))
    (cells : Fin outerEdges → Configuration innerEdges)
    (crossing : outer.crosses (inner.coarseConfiguration cells) = true)
    (cost : Fin (outerEdges * innerEdges) → ℝ) :
    (edgePathFamily (outer.substitute inner) (substitutionConfigurationEquiv cells)).shortest cost =
      (edgePathFamily outer (inner.coarseConfiguration cells)).shortest
        (fun edge => (edgePathFamily inner (cells edge)).shortest
          (fun child => cost (finProdFinEquiv (edge, child)))) := by
  classical
  have fineCrossing : (outer.substitute inner).crosses (substitutionConfigurationEquiv cells) = true := by
    simpa only [outer.substitute_crosses inner] using crossing
  apply le_antisymm
  · apply PathFamily.le_shortest
    intro coarsePath coarseMembership
    let childPath (edge : Fin outerEdges) := ((edgePathFamily inner (cells edge)).exists_minimizer
      (fun child => cost (finProdFinEquiv (edge, child)))).choose
    have childMembership (edge : Fin outerEdges) : childPath edge ∈ (edgePathFamily inner (cells edge)).paths :=
      ((edgePathFamily inner (cells edge)).exists_minimizer _).choose_spec.1
    have childMinimum (edge : Fin outerEdges) :
        PathFamily.pathCost (childPath edge) (fun child => cost (finProdFinEquiv (edge, child))) =
          (edgePathFamily inner (cells edge)).shortest (fun child => cost (finProdFinEquiv (edge, child))) :=
      ((edgePathFamily inner (cells edge)).exists_minimizer _).choose_spec.2.symm
    let selectedCells (edge : Fin outerEdges) : Configuration innerEdges :=
      if edge ∈ coarsePath then configurationOfPath (childPath edge) else fun _ => false
    have childCrossing (edge : Fin outerEdges) (retained : edge ∈ coarsePath) : inner.crosses (cells edge) = true :=
      edgePathFamily_used_edge outer outerSimple (inner.coarseConfiguration cells) coarseMembership retained
    have selectedCoarse : inner.coarseConfiguration selectedCells = configurationOfPath coarsePath := by
      funext edge
      by_cases retained : edge ∈ coarsePath
      · simp only [FiniteNetwork.coarseConfiguration, selectedCells, if_pos retained, configurationOfPath,
          decide_eq_true retained]
        exact (edgePathFamily_member_minimal inner innerSimple (cells edge)
          (childCrossing edge retained) (childMembership edge)).1
      · simp [FiniteNetwork.coarseConfiguration, selectedCells, retained, configurationOfPath, inner.crosses_all_closed]
    have selectedMinimal : MinimalCrossingConfiguration (outer.substitute inner)
        (substitutionConfigurationEquiv selectedCells) := by
      apply minimal_substitute_of_children outer inner selectedCells
      · rw [selectedCoarse]
        exact edgePathFamily_member_minimal outer outerSimple _ crossing coarseMembership
      · intro edge nonempty
        by_cases retained : edge ∈ coarsePath
        · simpa only [selectedCells, if_pos retained] using
            edgePathFamily_member_minimal inner innerSimple _ (childCrossing edge retained) (childMembership edge)
        · obtain ⟨child, opened⟩ := nonempty
          simp [selectedCells, retained] at opened
    have selectedSubset : ∀ leaf, substitutionConfigurationEquiv selectedCells leaf = true →
        substitutionConfigurationEquiv cells leaf = true := by
      intro leaf retained
      obtain ⟨⟨edge, child⟩, rfl⟩ := finProdFinEquiv.surjective leaf
      simp only [substitutionConfigurationEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] at retained ⊢
      by_cases active : edge ∈ coarsePath
      · simp only [selectedCells, if_pos active, configurationOfPath, decide_eq_true_eq] at retained
        exact edgePathFamily_used_edge inner innerSimple _ (childMembership edge) retained
      · simp [selectedCells, active] at retained
    have fineMembership : openEdges (substitutionConfigurationEquiv selectedCells) ∈
        (edgePathFamily (outer.substitute inner) (substitutionConfigurationEquiv cells)).paths := by
      apply (edgePathFamily_mem_iff_minimal _ substituteSimple _ fineCrossing _).mpr
      rw [configurationOfPath_openEdges]
      exact ⟨selectedMinimal, fun leaf member => selectedSubset leaf ((Finset.mem_filter.mp member).2)⟩
    calc
      _ ≤ PathFamily.pathCost (openEdges (substitutionConfigurationEquiv selectedCells)) cost :=
        PathFamily.shortest_le_pathCost _ _ fineMembership
      _ = _ := by
        rw [openEdges_substitution_pathCost]
        calc
          _ = ∑ edge ∈ coarsePath, PathFamily.pathCost (openEdges (selectedCells edge))
              (fun child => cost (finProdFinEquiv (edge, child))) :=
            (Finset.sum_subset (Finset.subset_univ coarsePath) (by
              intro edge _ retained
              simp [selectedCells, retained, openEdges, PathFamily.pathCost])).symm
          _ = _ := by
            apply Finset.sum_congr rfl
            intro edge retained
            simp only [selectedCells, if_pos retained, openEdges_configurationOfPath]
            exact childMinimum edge
  · apply PathFamily.le_shortest
    intro finePath fineMembership
    have fineMinimal := edgePathFamily_member_minimal _ substituteSimple _ fineCrossing fineMembership
    let pathCells := substitutionConfigurationEquiv.symm (configurationOfPath finePath)
    have pathConfiguration : substitutionConfigurationEquiv pathCells = configurationOfPath finePath :=
      substitutionConfigurationEquiv.apply_symm_apply _
    have pathMinimal : MinimalCrossingConfiguration (outer.substitute inner) (substitutionConfigurationEquiv pathCells) := by
      rwa [pathConfiguration]
    have pathSubset (edge : Fin outerEdges) (child : Fin innerEdges) (retained : pathCells edge child = true) :
        cells edge child = true := by
      have opened : configurationOfPath finePath (finProdFinEquiv (edge, child)) = true := by
        rw [← pathConfiguration]
        simpa only [substitutionConfigurationEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using retained
      have member := of_decide_eq_true opened
      have used := edgePathFamily_used_edge _ substituteSimple _ fineMembership member
      simpa only [substitutionConfigurationEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using used
    have coarseSubset (edge : Fin outerEdges) (retained : inner.coarseConfiguration pathCells edge = true) :
        inner.coarseConfiguration cells edge = true :=
      inner.crosses_mono (pathCells edge) (cells edge) (pathSubset edge) retained
    have coarseMinimal := minimal_substitute_coarse outer inner pathCells pathMinimal
    have coarseMembership : openEdges (inner.coarseConfiguration pathCells) ∈
        (edgePathFamily outer (inner.coarseConfiguration cells)).paths := by
      apply (edgePathFamily_mem_iff_minimal outer outerSimple _ crossing _).mpr
      rw [configurationOfPath_openEdges]
      exact ⟨coarseMinimal, fun edge member => coarseSubset edge ((Finset.mem_filter.mp member).2)⟩
    calc
      _ ≤ PathFamily.pathCost (openEdges (inner.coarseConfiguration pathCells))
          (fun edge => (edgePathFamily inner (cells edge)).shortest
            (fun child => cost (finProdFinEquiv (edge, child)))) :=
        PathFamily.shortest_le_pathCost _ _ coarseMembership
      _ ≤ ∑ edge, PathFamily.pathCost (openEdges (pathCells edge))
          (fun child => cost (finProdFinEquiv (edge, child))) := by
        simp only [PathFamily.pathCost, openEdges, Finset.sum_filter]
        apply Finset.sum_le_sum
        intro edge _
        by_cases active : inner.crosses (pathCells edge) = true
        · simp only [FiniteNetwork.coarseConfiguration, active, if_true]
          have nonempty : ∃ child, pathCells edge child = true := by
            by_contra empty
            have closed : pathCells edge = fun _ => false := by
              funext child
              cases retained : pathCells edge child
              · rfl
              · exact False.elim (empty ⟨child, retained⟩)
            rw [closed, inner.crosses_all_closed] at active
            contradiction
          have childMinimal := minimal_substitute_children outer inner pathCells pathMinimal edge nonempty
          have childMembership : openEdges (pathCells edge) ∈ (edgePathFamily inner (cells edge)).paths := by
            apply (edgePathFamily_mem_iff_minimal inner innerSimple _ (coarseSubset edge active) _).mpr
            rw [configurationOfPath_openEdges]
            exact ⟨childMinimal, fun child member => pathSubset edge child ((Finset.mem_filter.mp member).2)⟩
          simpa only [PathFamily.pathCost, openEdges, Finset.sum_filter] using
            PathFamily.shortest_le_pathCost (edgePathFamily inner (cells edge))
              (fun child => cost (finProdFinEquiv (edge, child))) childMembership
        · have closed := minimal_substitute_child_closed outer inner pathCells pathMinimal edge active
          simp only [FiniteNetwork.coarseConfiguration, active, if_false]
          simp [closed]
      _ = PathFamily.pathCost finePath cost := by
        rw [← openEdges_substitution_pathCost, pathConfiguration, openEdges_configurationOfPath]

end IGSIII.Chemical.Substitution
