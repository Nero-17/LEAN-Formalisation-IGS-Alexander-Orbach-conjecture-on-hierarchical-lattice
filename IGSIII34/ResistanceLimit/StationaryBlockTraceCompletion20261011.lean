import IGSIII34.ResistanceLimit.StationaryBlockResponseCompletion20261011
import IGSIII34.ResistanceLimit.SourceActualTrace
import IGSIII34.ResistanceLimit.SourceHarmonicFlatnessCompletion20261011

/-! Exact source-component traces through arbitrary-depth actual stationary
blocks. Both the connected crossing blocks and the two separate sides of a
noncrossing block are retained by source projection. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation
open IGSIII.Chemical.Substitution MeasureTheory

variable (rule : Rule)
  (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
  (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
  (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
  (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
  (stationary : ∀ address, electricalCell rule.network (marks (address, true))
    (fun edge => field (address ++ [edge])) = growth * field address)
  {outerVertices outerEdges : ℕ}
  (outer : Universality.FiniteNetwork outerVertices outerEdges)
  (addresses : Fin outerEdges → List (Fin rule.edges)) (coarse : Configuration outerEdges)
  (fine : ℕ) (scalar : ℝ) (scalarPositive : 0 < scalar)

include crossing in
theorem stationary_block_coarsens :
    (rule.generation fine).network.coarseConfiguration
      (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge)) = coarse := by
  funext edge
  exact markedGenerationConfiguration_crosses rule marks crossing fine (addresses edge) (coarse edge)

include growthPositive fieldPositive crossing stationary scalarPositive in
theorem stationary_block_coarse_resistance :
    coarseResistance (rule.generation fine).network
      (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))
      (fun edge => scalar * field (addresses edge.1 ++ generationEdgeAddress rule fine edge.2.val)) =
    (fun edge => scalar * growth ^ (fine + 1) * field (addresses edge.val)) := by
  funext edge
  have coarsens := stationary_block_coarsens rule marks crossing addresses coarse fine
  have retained : coarse edge.val = true := (congrFun coarsens edge.val).symm.trans edge.property
  change electricalCell (rule.generation fine).network
    (markedGenerationConfiguration rule marks fine (addresses edge.val) (coarse edge.val))
    (fun child => scalar * field (addresses edge.val ++ generationEdgeAddress rule fine child)) = _
  rw [retained, electricalCell_scale (rule.generation fine).network _
    (fun child => (fieldPositive _).le) scalarPositive.le,
    stationary_field_block_response rule marks field growth growthPositive fieldPositive crossing stationary]
  ring

include growthPositive fieldPositive crossing stationary scalarPositive in
theorem stationary_block_source_energy_le
    (potential : Fin (Fintype.card (outer.SubstitutionVertex (rule.generation fine).network)) → ℝ) :
    sourceComponentEnergy (network outer coarse)
      (fun edge => scalar * growth ^ (fine + 1) * field (addresses edge.val))
      (fun vertex => potential (Fintype.equivFin _ (Sum.inl vertex : outer.SubstitutionVertex (rule.generation fine).network))) ≤
    sourceComponentEnergy (network (outer.substitute (rule.generation fine).network)
      (substitutionConfigurationEquiv (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))))
      (fun edge => scalar * field (addresses ((substitutionOpenEdgeEquiv
        (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))).symm edge).1 ++
        generationEdgeAddress rule fine ((substitutionOpenEdgeEquiv
          (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))).symm edge).2.val)) potential := by
  have comparison := sourceComponentEnergy_le_actual_substitution_energy outer (rule.generation fine).network
    (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))
    (fun edge => scalar * field (addresses edge.1 ++ generationEdgeAddress rule fine edge.2.val))
    (fun edge => mul_pos scalarPositive (fieldPositive _)) potential
  rw [stationary_block_coarse_resistance rule marks field growth growthPositive fieldPositive crossing stationary
    addresses coarse fine scalar scalarPositive,
    stationary_block_coarsens rule marks crossing addresses coarse fine] at comparison
  exact comparison

include growthPositive fieldPositive crossing stationary scalarPositive in
theorem exists_stationary_block_source_minimizer
    (boundary : Fin outerVertices → ℝ) :
    ∃ potential : Fin (Fintype.card (outer.SubstitutionVertex (rule.generation fine).network)) → ℝ,
      (∀ vertex, (outer.openGraph coarse).Reachable outer.source vertex →
        potential (Fintype.equivFin _ (Sum.inl vertex : outer.SubstitutionVertex (rule.generation fine).network)) = boundary vertex) ∧
      sourceComponentEnergy (network (outer.substitute (rule.generation fine).network)
        (substitutionConfigurationEquiv (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))))
        (fun edge => scalar * field (addresses ((substitutionOpenEdgeEquiv
          (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))).symm edge).1 ++
          generationEdgeAddress rule fine ((substitutionOpenEdgeEquiv
            (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))).symm edge).2.val)) potential =
      sourceComponentEnergy (network outer coarse)
        (fun edge => scalar * growth ^ (fine + 1) * field (addresses edge.val)) boundary := by
  obtain ⟨potential, restriction, minimizing⟩ := exists_actual_sourceComponentEnergy_minimizer outer (rule.generation fine).network
    (fun edge => markedGenerationConfiguration rule marks fine (addresses edge) (coarse edge))
    (fun edge => scalar * field (addresses edge.1 ++ generationEdgeAddress rule fine edge.2.val))
    (fun edge => mul_pos scalarPositive (fieldPositive _)) boundary
  rw [stationary_block_coarse_resistance rule marks field growth growthPositive fieldPositive crossing stationary
    addresses coarse fine scalar scalarPositive,
    stationary_block_coarsens rule marks crossing addresses coarse fine] at minimizing
  refine ⟨potential, ?_, minimizing⟩
  intro vertex retained
  apply restriction vertex
  rw [graph_eq_openGraph, stationary_block_coarsens rule marks crossing addresses coarse fine]
  exact retained

end
end IGSIII34.ResistanceLimit
