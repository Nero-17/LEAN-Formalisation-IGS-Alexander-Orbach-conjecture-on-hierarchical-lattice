import IGSIII34.ResistanceLimit.CellZeroExtension
import IGSIII34.ResistanceLimit.SelectedComponentEnergy
import IGSIII34.ResistanceLimit.Rayleigh

set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation

/-- An actual retained side with zero planted values extends by zero to the
retained root graph with exactly its intrinsic energy. The source and target
components of B are treated separately by `sourceSide`. -/
theorem side_cellZeroExtension_source_energy
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (chosen : Fin outerEdges) (sourceSide : Bool) (supplied : Fin innerVertices → ℝ)
    (atSource : sourceProjection (sideNetwork (network inner (configuration chosen)) sourceSide)
      supplied inner.source = 0)
    (atTarget : sourceProjection (sideNetwork (network inner (configuration chosen)) sourceSide)
      supplied inner.target = 0)
    (anchorRetained : (substitutedNetwork outer inner configuration).graph.Reachable
      (substitutedNetwork outer inner configuration).source
      (outer.cellVertex inner chosen (sideNetwork (network inner (configuration chosen)) sourceSide).source)) :
    sourceComponentEnergy (substitutedNetwork outer inner configuration) resistance
      (cellZeroExtension outer inner chosen
        (sourceProjection (sideNetwork (network inner (configuration chosen)) sourceSide) supplied)) =
    sourceComponentEnergy (sideNetwork (network inner (configuration chosen)) sourceSide)
      (fun edge => resistance ⟨chosen, edge⟩) supplied := by
  classical
  let vertices : Fin innerVertices ↪ outer.SubstitutionVertex inner :=
    ⟨outer.cellVertex inner chosen, outer.cellVertex_injective inner chosen⟩
  let edges : {child : Fin innerEdges // configuration chosen child = true} ↪
      (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) :=
    ⟨fun edge => ⟨chosen, edge⟩, fun first last equality => by
      exact eq_of_heq (Sigma.mk.inj_iff.mp equality).2⟩
  let hom := networkEmbeddingGraphHom (sideNetwork (network inner (configuration chosen)) sourceSide)
    (substitutedNetwork outer inner configuration) vertices edges (by
      intro edge
      rw [sideNetwork_endpoint]
      rfl)
  have projectionIdentity : sourceProjection (substitutedNetwork outer inner configuration)
      (cellZeroExtension outer inner chosen
        (sourceProjection (sideNetwork (network inner (configuration chosen)) sourceSide) supplied)) =
      cellZeroExtension outer inner chosen
        (sourceProjection (sideNetwork (network inner (configuration chosen)) sourceSide) supplied) := by
    funext vertex
    by_cases retained : (substitutedNetwork outer inner configuration).graph.Reachable
        (substitutedNetwork outer inner configuration).source vertex
    · simp only [sourceProjection, if_pos retained]
    · rw [sourceProjection, if_neg retained]
      cases vertex with
      | inl vertex => rfl
      | inr pair =>
          rcases pair with ⟨other, inside⟩
          by_cases same : other = chosen
          · subst other
            by_cases localRetained : (sideNetwork (network inner (configuration chosen)) sourceSide).graph.Reachable
                (sideNetwork (network inner (configuration chosen)) sourceSide).source inside.val
            · have mapped := localRetained.map hom
              have global := anchorRetained.trans mapped
              have identity : outer.cellVertex inner chosen inside.val = Sum.inr (chosen, inside) := by
                simp only [Universality.FiniteNetwork.cellVertex, dif_neg inside.property.1, dif_neg inside.property.2]
                rfl
              change (substitutedNetwork outer inner configuration).graph.Reachable
                (substitutedNetwork outer inner configuration).source
                (outer.cellVertex inner chosen inside.val) at global
              rw [identity] at global
              exact (retained global).elim
            · simp only [cellZeroExtension, Sum.elim_inr, ↓reduceIte, sourceProjection, if_neg localRetained]
          · simp only [cellZeroExtension, Sum.elim_inr, if_neg same]
  rw [sourceComponentEnergy_eq_projectedEnergy, projectionIdentity,
    cellZeroExtension_energy outer inner configuration resistance chosen _ atSource atTarget]
  rw [sourceComponentEnergy_eq_projectedEnergy,
    sideNetwork_potentialEnergy]

end
end IGSIII34.ResistanceLimit
