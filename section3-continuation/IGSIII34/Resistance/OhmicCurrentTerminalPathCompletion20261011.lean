import IGSIII34.Resistance.OhmicClosedCutCompletion20261011
import IGSIII34.Resistance.DescendingPotentialPathsCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]

theorem positive_ohmic_current_terminal_path_completion20261011
    (network : FiniteNetwork Vertex Edge) (resistance current : Edge → ℝ) (potential : Vertex → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (unitFlow : current ∈ network.unitFlows)
    (ohm : ∀ edge, resistance edge * current edge = potential (network.endpoint edge).1 - potential (network.endpoint edge).2)
    (edge : Edge) (currentPositive : 0 < current edge) :
    ∃ path : network.graph.Walk network.source network.target, path.IsPath ∧
      s((network.endpoint edge).1, (network.endpoint edge).2) ∈ path.edges := by
  classical
  have decrease : potential (network.endpoint edge).2 < potential (network.endpoint edge).1 := by
    have product := mul_pos (positive edge) currentPositive
    rw [ohm] at product
    linarith
  have adjacent : network.graph.Adj (network.endpoint edge).1 (network.endpoint edge).2 := by
    refine ⟨?_, edge, Or.inl rfl⟩
    intro equal
    rw [equal] at decrease
    exact (lt_irrefl _) decrease
  let forward : Set Vertex := {vertex | Relation.ReflTransGen
    (descendingPotentialStepCompletion20261011 network potential) (network.endpoint edge).2 vertex}
  have forwardClosed : ∀ first last, first ∈ forward → network.graph.Adj first last →
      potential last < potential first → last ∈ forward := by
    intro first last reachable adjacency drop
    exact reachable.tail ⟨adjacency, drop⟩
  have firstOutside : (network.endpoint edge).1 ∉ forward := by
    intro reachable
    have comparison := descendingPotentialReachable_le_completion20261011 network potential reachable
    linarith
  have forwardTerminals := ohmic_closed_cut_terminals_completion20261011 network forward resistance current potential
    positive unitFlow ohm forwardClosed edge currentPositive firstOutside Relation.ReflTransGen.refl
  let backward : Set Vertex := {vertex | Relation.ReflTransGen
    (descendingPotentialStepCompletion20261011 network potential) vertex (network.endpoint edge).1}
  have complementClosed : ∀ first last, first ∈ backwardᶜ → network.graph.Adj first last →
      potential last < potential first → last ∈ backwardᶜ := by
    intro first last outside adjacency drop reachable
    exact outside (reachable.head ⟨adjacency, drop⟩)
  have lastOutside : (network.endpoint edge).2 ∉ backward := by
    intro reachable
    have comparison := descendingPotentialReachable_le_completion20261011 network potential reachable
    linarith
  have backwardTerminals := ohmic_closed_cut_terminals_completion20261011 network backwardᶜ resistance current potential
    positive unitFlow ohm complementClosed edge currentPositive
    (fun outside => outside Relation.ReflTransGen.refl) lastOutside
  have before : Relation.ReflTransGen (descendingPotentialStepCompletion20261011 network potential)
      network.source (network.endpoint edge).1 := Classical.not_not.mp backwardTerminals.1
  exact descendingPotentialReachable_path_through_edge_completion20261011 network potential _ _ adjacent decrease before forwardTerminals.2

def reverseTerminalsCompletion20261011 (network : FiniteNetwork Vertex Edge) : FiniteNetwork Vertex Edge where
  endpoint := network.endpoint
  source := network.target
  target := network.source
  distinct := network.distinct.symm

/-- Every nonzero Ohmic unit-current edge belongs to a genuine simple
terminal path, including edges whose stored orientation opposes the flow. -/
theorem nonzero_ohmic_current_terminal_path_completion20261011
    (network : FiniteNetwork Vertex Edge) (resistance current : Edge → ℝ) (potential : Vertex → ℝ)
    (positive : ∀ edge, 0 < resistance edge) (unitFlow : current ∈ network.unitFlows)
    (ohm : ∀ edge, resistance edge * current edge = potential (network.endpoint edge).1 - potential (network.endpoint edge).2)
    (edge : Edge) (nonzero : current edge ≠ 0) :
    ∃ path : network.graph.Walk network.source network.target, path.IsPath ∧
      s((network.endpoint edge).1, (network.endpoint edge).2) ∈ path.edges := by
  rcases lt_or_gt_of_ne nonzero with negative | positiveCurrent
  · have reversedFlow : (fun index => -current index) ∈ (reverseTerminalsCompletion20261011 network).unitFlows := by
      intro vertex
      change network.divergence (fun index => -current index) vertex =
        (if vertex = network.target then 1 else 0) - (if vertex = network.source then 1 else 0)
      rw [network.divergence_neg, unitFlow vertex]
      ring
    have reversedOhm : ∀ index, resistance index * (-current index) =
        (-potential (network.endpoint index).1) - (-potential (network.endpoint index).2) := by
      intro index
      nlinarith [ohm index]
    obtain ⟨path, simple, contains⟩ := positive_ohmic_current_terminal_path_completion20261011
      (reverseTerminalsCompletion20261011 network) resistance (fun index => -current index) (fun vertex => -potential vertex)
      positive reversedFlow reversedOhm edge (neg_pos.mpr negative)
    refine ⟨path.reverse, simple.reverse, ?_⟩
    change s(((reverseTerminalsCompletion20261011 network).endpoint edge).1,
      ((reverseTerminalsCompletion20261011 network).endpoint edge).2) ∈ path.reverse.edges
    simpa only [SimpleGraph.Walk.edges_reverse, List.mem_reverse] using contains
  · exact positive_ohmic_current_terminal_path_completion20261011 network resistance current potential positive unitFlow ohm edge positiveCurrent

end
end IGSIII34.Resistance.FiniteNetwork
