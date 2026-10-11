import IGSIII34.ResistanceLimit.SourceTrace
import IGSIII34.ResistanceLimit.SeparatedTerminalPotential

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation

def swapNetworkTerminals {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges) :
    Universality.FiniteNetwork vertices edges :=
  { network with
    source := network.target
    target := network.source
    terminals_distinct := network.terminals_distinct.symm }

/-- Retaining the target side is as compatible as retaining the source side.
This keeps both components of a B socket as independent energy summands,
without making any probabilistic independence assertion. -/
theorem side_sourceComponentEnergy_le_substituted_energy
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : Universality.FiniteNetwork outerVertices outerEdges)
    (inner : Universality.FiniteNetwork innerVertices innerEdges)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (resistance : (Σ edge : Fin outerEdges, {child : Fin innerEdges // configuration edge child = true}) → ℝ)
    (positive : ∀ edge, 0 < resistance edge)
    (sourceSide : Bool) (potential : outer.SubstitutionVertex inner → ℝ) :
    sourceComponentEnergy (sideNetwork (network outer (inner.coarseConfiguration configuration)) sourceSide)
      (coarseResistance inner configuration resistance) (fun vertex => potential (Sum.inl vertex)) ≤
    sourceComponentEnergy (sideNetwork (substitutedNetwork outer inner configuration) sourceSide)
      resistance potential := by
  cases sourceSide with
  | true => exact sourceComponentEnergy_le_substituted_energy outer inner configuration resistance positive potential
  | false =>
      exact sourceComponentEnergy_le_substituted_energy (swapNetworkTerminals outer) inner
        configuration resistance positive potential

end
end IGSIII34.ResistanceLimit
