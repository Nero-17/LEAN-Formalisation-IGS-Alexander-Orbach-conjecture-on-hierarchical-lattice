import IGSIII34.ResistanceLimit.SideCellZeroExtension
import IGSIII34.ResistanceLimit.SourceActualTrace

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation

theorem actual_side_cellZeroExtension_source_energy
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (chosen : Fin outerEdges) (sourceSide : Bool) (supplied : Fin innerVertices → ℝ)
    (atSource : sourceProjection (sideNetwork (network inner (configuration chosen)) sourceSide) supplied inner.source = 0)
    (atTarget : sourceProjection (sideNetwork (network inner (configuration chosen)) sourceSide) supplied inner.target = 0)
    (anchorRetained : (outer.substitute inner).openGraph (substitutionConfigurationEquiv configuration) |>.Reachable
      (outer.substitute inner).source
      (Fintype.equivFin _ (outer.cellVertex inner chosen (sideNetwork (network inner (configuration chosen)) sourceSide).source))) :
    sourceComponentEnergy (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
      (fun edge => resistance ((substitutionOpenEdgeEquiv configuration).symm edge))
      (fun vertex => cellZeroExtension outer inner chosen
        (sourceProjection (sideNetwork (network inner (configuration chosen)) sourceSide) supplied)
        ((Fintype.equivFin _).symm vertex)) =
    sourceComponentEnergy (sideNetwork (network inner (configuration chosen)) sourceSide)
      (fun edge => resistance ⟨chosen, edge⟩) supplied := by
  rw [sourceComponentEnergy_reindex (substitutedNetwork outer inner configuration)
    (network (outer.substitute inner) (substitutionConfigurationEquiv configuration))
    (Fintype.equivFin _) (substitutionOpenEdgeEquiv configuration) (by
      intro edge
      exact outer.substitute_endpoint inner edge.1 edge.2.val) rfl]
  simp only [Equiv.symm_apply_apply]
  have unindexed := anchorRetained.map (outer.substitutionGraphIso inner configuration).symm.toHom
  change (outer.substitutedGraph inner configuration).Reachable
    ((Fintype.equivFin _).symm (Fintype.equivFin _ (Sum.inl outer.source)))
    ((Fintype.equivFin _).symm (Fintype.equivFin _
      (outer.cellVertex inner chosen (sideNetwork (network inner (configuration chosen)) sourceSide).source))) at unindexed
  simp only [Equiv.symm_apply_apply] at unindexed
  rw [← substitutedNetwork_graph_eq] at unindexed
  exact side_cellZeroExtension_source_energy outer inner configuration resistance chosen sourceSide supplied
    atSource atTarget unindexed

end
end IGSIII34.ResistanceLimit
