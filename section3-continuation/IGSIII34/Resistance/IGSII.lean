import IGSIII34.Resistance.Dirichlet
import Universality.Graph.DirichletEnergy

/-!
# The finite electrical functional agrees with IGS II

This is a bridge between concrete network definitions, not an identification
certificate assumed among the network fields.
-/

set_option autoImplicit false

namespace IGSIII34.Resistance
noncomputable section

def ofIGSII {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges) :
    FiniteNetwork (Fin vertices) (Fin edges) where
  endpoint := network.endpoint
  source := network.source
  target := network.target
  distinct := network.terminals_distinct

theorem ofIGSII_graph {vertices edges : ℕ} (network : Universality.FiniteNetwork vertices edges) :
    (ofIGSII network).graph = network.fullGraph := by
  ext first second
  simp [FiniteNetwork.graph, ofIGSII, Universality.FiniteNetwork.fullGraph,
    Universality.FiniteNetwork.openGraph]

theorem ofIGSII_unitConductance {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) :
    (ofIGSII network).effectiveConductance (fun _ => 1) = network.unitConductance := by
  unfold FiniteNetwork.effectiveConductance Universality.FiniteNetwork.unitConductance
  congr 1
  ext value
  simp [FiniteNetwork.unitPotentialEnergies, Universality.FiniteNetwork.unitPotentialEnergies,
    FiniteNetwork.potentialEnergy, Universality.FiniteNetwork.dirichletEnergy, ofIGSII]

theorem ofIGSII_unitEffectiveResistance {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges)
    (connected : network.fullGraph.Reachable network.source network.target) :
    (ofIGSII network).effectiveResistance (fun _ => 1) = network.unitEffectiveResistance connected := by
  have adaptedConnected : (ofIGSII network).graph.Reachable
      (ofIGSII network).source (ofIGSII network).target := by
    change (ofIGSII network).graph.Reachable network.source network.target
    rw [ofIGSII_graph]
    exact connected
  rw [(ofIGSII network).effectiveResistance_eq_inverseConductance adaptedConnected (fun _ => zero_lt_one),
    ofIGSII_unitConductance]
  rfl

end
end IGSIII34.Resistance
