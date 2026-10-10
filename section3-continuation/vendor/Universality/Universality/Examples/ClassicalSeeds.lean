import Universality.Graph.ClassicalRule
import Universality.Examples.AdmissibleMassCounterexample

namespace Universality
noncomputable section
open FiniteNetwork

def wheatstoneCanonicalWalk (edge : Fin 5) :
    wheatstoneNetwork.fullGraph.Walk wheatstoneNetwork.source wheatstoneNetwork.target :=
  match edge.val with
  | 0 => .cons (by decide : wheatstoneNetwork.fullGraph.Adj 0 2) (.cons (by decide : wheatstoneNetwork.fullGraph.Adj 2 1) (.nil))
  | 1 => .cons (by decide : wheatstoneNetwork.fullGraph.Adj 0 2) (.cons (by decide : wheatstoneNetwork.fullGraph.Adj 2 1) (.nil))
  | 2 => .cons (by decide : wheatstoneNetwork.fullGraph.Adj 0 3) (.cons (by decide : wheatstoneNetwork.fullGraph.Adj 3 1) (.nil))
  | 3 => .cons (by decide : wheatstoneNetwork.fullGraph.Adj 0 3) (.cons (by decide : wheatstoneNetwork.fullGraph.Adj 3 1) (.nil))
  | _ => .cons (by decide : wheatstoneNetwork.fullGraph.Adj 0 2) (.cons (by decide : wheatstoneNetwork.fullGraph.Adj 2 3) (.cons (by decide : wheatstoneNetwork.fullGraph.Adj 3 1) (.nil)))

theorem wheatstoneRule_classical : wheatstoneRule.Classical where
  connected := by
    intro vertex
    apply (wheatstoneNetwork.fullGraph.reachableDecide_eq_true wheatstoneNetwork.source vertex).mp
    have h : ∀ vertex, wheatstoneNetwork.fullGraph.reachableDecide wheatstoneNetwork.source vertex = true := by decide
    exact h vertex
  simple := by decide
  canonical := by
    intro edge
    refine ⟨wheatstoneCanonicalWalk edge, ?_, ?_⟩
    · apply SimpleGraph.Walk.IsPath.mk'
      fin_cases edge <;> decide
    · fin_cases edge <;> decide
  scale := wheatstoneRule_massAdmissible.scale
  cut := wheatstoneRule_massAdmissible.cut
  symmetric := ⟨wheatstoneTerminalSymmetry,
    by intro vertex; fin_cases vertex <;> decide, wheatstone_terminal_symmetry_source⟩

def oppositeWheatstoneCanonicalWalk (edge : Fin 13) :
    oppositeWheatstoneNetwork.fullGraph.Walk oppositeWheatstoneNetwork.source oppositeWheatstoneNetwork.target :=
  match edge.val with
  | 0 => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 4) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 4 2) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 2 1) (.nil)))
  | 1 => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 3) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 3 6) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 6 1) (.nil)))
  | 2 => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 4) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 4 2) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 2 3) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 3 6) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 6 1) (.nil)))))
  | 3 => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 4) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 4 2) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 2 1) (.nil)))
  | 4 => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 4) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 4 2) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 2 1) (.nil)))
  | 5 => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 5) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 5 2) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 2 1) (.nil)))
  | 6 => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 5) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 5 2) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 2 1) (.nil)))
  | 7 => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 4) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 4 5) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 5 2) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 2 1) (.nil))))
  | 8 => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 3) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 3 6) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 6 1) (.nil)))
  | 9 => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 3) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 3 6) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 6 1) (.nil)))
  | 10 => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 3) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 3 7) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 7 1) (.nil)))
  | 11 => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 3) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 3 7) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 7 1) (.nil)))
  | _ => .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 3) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 3 6) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 6 7) (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 7 1) (.nil))))

theorem oppositeWheatstoneRule_classical : oppositeWheatstoneRule.Classical where
  connected := by
    intro vertex
    apply (oppositeWheatstoneNetwork.fullGraph.reachableDecide_eq_true oppositeWheatstoneNetwork.source vertex).mp
    have h : ∀ vertex, oppositeWheatstoneNetwork.fullGraph.reachableDecide oppositeWheatstoneNetwork.source vertex = true := by decide
    exact h vertex
  simple := by decide
  canonical := by
    intro edge
    refine ⟨oppositeWheatstoneCanonicalWalk edge, ?_, ?_⟩
    · apply SimpleGraph.Walk.IsPath.mk'
      fin_cases edge <;> decide
    · fin_cases edge <;> decide
  scale := oppositeWheatstoneRule_massAdmissible.scale
  cut := oppositeWheatstoneRule_massAdmissible.cut
  symmetric := ⟨oppositeWheatstoneTerminalSymmetry,
    by intro vertex; fin_cases vertex <;> decide, oppositeWheatstone_terminal_symmetry_source⟩

end
end Universality
