import Universality.Graph.ClassicalRule
import Mathlib.Tactic.FinCases

namespace Universality
open FiniteNetwork

/-- Wheatstone with its middle edge replaced by another Wheatstone cell. -/
def centralWheatstoneNetwork : FiniteNetwork 6 9 where
  endpoint := ![(0, 2), (2, 1), (0, 3), (3, 1), (2, 4), (4, 3), (2, 5), (5, 3), (4, 5)]
  source := 0
  target := 1
  terminals_distinct := by decide
  loopless := by decide

def centralWheatstoneRule : Rule := ⟨6, 9, centralWheatstoneNetwork⟩

def centralWheatstoneTerminalSymmetry : centralWheatstoneNetwork.NetworkSymmetry where
  vertex := Equiv.swap 0 1
  edge := (Equiv.swap 0 1).trans (Equiv.swap 2 3)
  endpoint := by decide

def centralWheatstoneCanonicalWalk (edge : Fin 9) :
    centralWheatstoneNetwork.fullGraph.Walk centralWheatstoneNetwork.source centralWheatstoneNetwork.target :=
  if edge.val < 2 then
    .cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 0 2)
      (.cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 2 1) .nil)
  else if edge.val < 4 then
    .cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 0 3)
      (.cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 3 1) .nil)
  else if edge.val < 6 then
    .cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 0 2)
      (.cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 2 4)
        (.cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 4 3)
          (.cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 3 1) .nil)))
  else if edge.val < 8 then
    .cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 0 2)
      (.cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 2 5)
        (.cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 5 3)
          (.cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 3 1) .nil)))
  else
    .cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 0 2)
      (.cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 2 4)
        (.cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 4 5)
          (.cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 5 3)
            (.cons (by decide : centralWheatstoneNetwork.fullGraph.Adj 3 1) .nil))))

def centralWheatstoneDistanceCertificate : centralWheatstoneNetwork.DistanceCertificate where
  length := 2
  height := ![0, 2, 1, 1, 1, 1]
  source_height := rfl
  target_height := rfl
  edge_bound := by decide
  walk := centralWheatstoneCanonicalWalk 0
  walk_length := rfl

theorem centralWheatstone_terminal_distance :
    centralWheatstoneNetwork.fullGraph.dist centralWheatstoneNetwork.source centralWheatstoneNetwork.target = 2 :=
  centralWheatstoneDistanceCertificate.distance_eq

theorem centralWheatstoneRule_classical : centralWheatstoneRule.Classical where
  connected := by
    intro vertex
    apply (centralWheatstoneNetwork.fullGraph.reachableDecide_eq_true centralWheatstoneNetwork.source vertex).mp
    have h : ∀ vertex, centralWheatstoneNetwork.fullGraph.reachableDecide centralWheatstoneNetwork.source vertex = true := by decide
    exact h vertex
  simple := by decide
  canonical := by
    intro edge
    refine ⟨centralWheatstoneCanonicalWalk edge, ?_, ?_⟩
    · apply SimpleGraph.Walk.IsPath.mk'
      fin_cases edge <;> decide
    · fin_cases edge <;> decide
  scale := by
    change 1 < centralWheatstoneNetwork.fullGraph.dist centralWheatstoneNetwork.source centralWheatstoneNetwork.target
    rw [centralWheatstone_terminal_distance]
    norm_num
  cut := by decide
  symmetric := ⟨centralWheatstoneTerminalSymmetry,
    by intro vertex; fin_cases vertex <;> decide, by decide⟩

end Universality
