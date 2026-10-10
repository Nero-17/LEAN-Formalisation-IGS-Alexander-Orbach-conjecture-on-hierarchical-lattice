import Universality.Graph.Section5Symmetry
import Universality.Graph.Section5Distance
import Universality.Examples.ClassicalSeeds
import Universality.Section5.WheatstoneGrammar
import Universality.Percolation.ClassicalCriticalPoint

set_option backward.isDefEq.respectTransparency false

namespace Universality.Section5
noncomputable section
open FiniteNetwork

theorem TerminalGraphProperties.ofClassical {rule : Rule} (properties : rule.Classical) :
    TerminalGraphProperties rule :=
  ⟨properties.connected, properties.simple, properties.canonical, properties.symmetric⟩

theorem wheatstoneRule_terminalProperties (a b c : Rule)
    (first : TerminalGraphProperties a) (second : TerminalGraphProperties b)
    (central : TerminalGraphProperties c) : TerminalGraphProperties (wheatstoneRule a b c) where
  connected := wheatstoneNetwork.heterogeneousSubstitute_all_vertices_connected
    (fun edge => (![a,b,b,a,c] edge).network) Universality.wheatstoneRule_classical.connected (by
      intro edge
      fin_cases edge
      · exact first.connected
      · exact second.connected
      · exact second.connected
      · exact first.connected
      · exact central.connected)
  simple := wheatstoneNetwork.heterogeneousSubstitute_simple
    (fun edge => (![a,b,b,a,c] edge).network) Universality.wheatstoneRule_classical.simple (by
      intro edge
      fin_cases edge
      · exact first.simple
      · exact second.simple
      · exact second.simple
      · exact first.simple
      · exact central.simple)
  canonical := wheatstoneNetwork.heterogeneousSubstitute_canonical
    (fun edge => (![a,b,b,a,c] edge).network) Universality.wheatstoneRule_classical.simple (by
      intro edge
      fin_cases edge
      · exact first.simple
      · exact second.simple
      · exact second.simple
      · exact first.simple
      · exact central.simple) (by
      intro edge
      fin_cases edge
      · exact first.connected _
      · exact second.connected _
      · exact second.connected _
      · exact first.connected _
      · exact central.connected _) Universality.wheatstoneRule_classical.canonical (by
      intro edge
      fin_cases edge
      · exact first.canonical
      · exact second.canonical
      · exact second.canonical
      · exact first.canonical
      · exact central.canonical)
  symmetric :=
    ⟨(wheatstoneTerminalInvolution a b c first.involution second.involution central.involution).symmetry,
      (wheatstoneTerminalInvolution a b c first.involution second.involution central.involution).vertex_involutive,
      (wheatstoneTerminalInvolution a b c first.involution second.involution central.involution).source⟩

theorem wheatstoneRule_classical (a b c : Rule)
    (first : TerminalGraphProperties a) (second : TerminalGraphProperties b)
    (central : TerminalGraphProperties c) : (wheatstoneRule a b c).Classical where
  connected := (wheatstoneRule_terminalProperties a b c first second central).connected
  simple := (wheatstoneRule_terminalProperties a b c first second central).simple
  canonical := (wheatstoneRule_terminalProperties a b c first second central).canonical
  symmetric := (wheatstoneRule_terminalProperties a b c first second central).symmetric
  cut := wheatstoneNetwork.heterogeneousSubstitute_cut
    (fun edge => (![a,b,b,a,c] edge).network) Universality.wheatstoneRule_classical.cut (by
      intro edge
      fin_cases edge
      · exact first.connected _
      · exact second.connected _
      · exact second.connected _
      · exact first.connected _
      · exact central.connected _)
  scale := by
    rw [wheatstoneRule_distance a b c (first.connected _) (second.connected _) (central.connected _)]
    have first_positive := (first.connected a.network.target).pos_dist_of_ne a.network.terminals_distinct
    have second_positive := (second.connected b.network.target).pos_dist_of_ne b.network.terminals_distinct
    have central_positive := (central.connected c.network.target).pos_dist_of_ne c.network.terminals_distinct
    omega

def singleEdgeTerminalInvolution : TerminalInvolution singleEdgeRule where
  symmetry := {
    vertex := Equiv.swap (0 : Fin 2) (1 : Fin 2)
    edge := Equiv.refl _
    endpoint := by decide }
  vertex_involutive := by intro vertex; simp
  edge_involutive := by intro edge; rfl
  source := by decide

theorem singleEdgeRule_terminalProperties : TerminalGraphProperties singleEdgeRule where
  connected := by
    intro vertex
    fin_cases vertex
    · exact .refl _
    · exact (show singleEdgeNetwork.fullGraph.Adj 0 1 from by decide).reachable
  simple := by decide
  canonical := by
    intro edge
    refine ⟨.cons (by decide : singleEdgeNetwork.fullGraph.Adj 0 1) .nil, ?_, ?_⟩
    · apply SimpleGraph.Walk.IsPath.mk'
      decide
    · fin_cases edge <;> decide
  symmetric := ⟨singleEdgeTerminalInvolution.symmetry,
    singleEdgeTerminalInvolution.vertex_involutive, singleEdgeTerminalInvolution.source⟩

theorem WheatstoneExpression.terminalProperties (expression : WheatstoneExpression) :
    TerminalGraphProperties expression.rule := by
  induction expression with
  | edge => exact singleEdgeRule_terminalProperties
  | node a b c first second central => exact wheatstoneRule_terminalProperties _ _ _ first second central

theorem WheatstoneExpression.classical (expression : WheatstoneExpression) (nontrivial : expression ≠ .edge) :
    expression.rule.Classical := by
  cases expression with
  | edge => exact (nontrivial rfl).elim
  | node a b c => exact wheatstoneRule_classical _ _ _ a.terminalProperties b.terminalProperties c.terminalProperties

theorem WheatstoneExpression.unique_interior_fixed_point (expression : WheatstoneExpression)
    (nontrivial : expression ≠ .edge) (p : ℝ) (positive : 0 < p) (less_one : p < 1)
    (fixed : expression.rule.network.reliability p = p) : p = 1 / 2 :=
  expression.rule.network.interior_fixed_point_unique p (1 / 2) positive less_one
    (by norm_num) (by norm_num) fixed expression.fixed_half (expression.classical nontrivial).scale

end
end Universality.Section5
