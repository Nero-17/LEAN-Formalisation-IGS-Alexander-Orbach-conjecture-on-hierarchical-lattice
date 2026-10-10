import Universality.Graph.ClassicalRule
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace IGSIII4.LongDiamond
noncomputable section
open Universality Universality.FiniteNetwork

/-- The twenty-cycle with opposite terminals. The intermediate degree-two
vertices 5 and 15 give the standard diamond's two corners, and each of its
four edges is a chain of five unit edges. -/
def network : FiniteNetwork 20 20 where
  endpoint edge := (edge, edge + 1)
  source := 0
  target := 10
  terminals_distinct := by decide
  loopless := by decide

def rule : Rule := ⟨20, 20, network⟩

def lowerWalk : network.fullGraph.Walk network.source network.target :=
  SimpleGraph.Walk.ofSupport ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List (Fin 20)) (by decide) (by decide)

def upperWalk : network.fullGraph.Walk network.source network.target :=
  SimpleGraph.Walk.ofSupport ([0, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10] : List (Fin 20)) (by decide) (by decide)

theorem lowerWalk_path : lowerWalk.IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List (Fin 20)).Nodup
  decide

theorem upperWalk_path : upperWalk.IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  change ([0, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10] : List (Fin 20)).Nodup
  decide

theorem lowerWalk_length : lowerWalk.length = 10 := by
  decide

theorem upperWalk_length : upperWalk.length = 10 := by
  decide

def terminalSymmetry : network.NetworkSymmetry where
  vertex := Equiv.addRight (10 : Fin 20)
  edge := Equiv.addRight (10 : Fin 20)
  endpoint := by decide

def distanceCertificate : network.DistanceCertificate where
  length := 10
  height := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1]
  source_height := rfl
  target_height := rfl
  edge_bound := by decide
  walk := lowerWalk
  walk_length := lowerWalk_length

theorem terminal_distance : network.fullGraph.dist network.source network.target = 10 :=
  distanceCertificate.distance_eq

theorem classical : rule.Classical where
  connected := by
    intro vertex
    have coverage : ∀ vertex : Fin 20, vertex ∈ lowerWalk.support ∨ vertex ∈ upperWalk.support := by decide
    rcases coverage vertex with onLower | onUpper
    · exact ⟨lowerWalk.takeUntil vertex onLower⟩
    · exact ⟨upperWalk.takeUntil vertex onUpper⟩
  simple := by decide
  canonical := by
    intro edge
    by_cases firstHalf : edge.val < 10
    · refine ⟨lowerWalk, lowerWalk_path, ?_⟩
      have membership : ∀ edge : Fin 20, edge.val < 10 →
          s((network.endpoint edge).1, (network.endpoint edge).2) ∈ lowerWalk.edges := by decide
      exact membership edge firstHalf
    · refine ⟨upperWalk, upperWalk_path, ?_⟩
      have membership : ∀ edge : Fin 20, ¬ edge.val < 10 →
          s((network.endpoint edge).1, (network.endpoint edge).2) ∈ upperWalk.edges := by decide
      exact membership edge firstHalf
  scale := by
    change 1 < network.fullGraph.dist network.source network.target
    rw [terminal_distance]
    decide
  cut := by
    intro edge
    apply (network.crosses_eq_true (onlyClosed edge)).mpr
    by_cases firstHalf : edge.val < 10
    · have chain : ∀ edge : Fin 20, edge.val < 10 →
          ([0, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10] : List (Fin 20)).IsChain (network.openGraph (onlyClosed edge)).Adj := by decide
      exact ⟨SimpleGraph.Walk.ofSupport ([0, 19, 18, 17, 16, 15, 14, 13, 12, 11, 10] : List (Fin 20)) (by decide) (chain edge firstHalf)⟩
    · have chain : ∀ edge : Fin 20, ¬ edge.val < 10 →
          ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List (Fin 20)).IsChain (network.openGraph (onlyClosed edge)).Adj := by decide
      exact ⟨SimpleGraph.Walk.ofSupport ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10] : List (Fin 20)) (by decide) (chain edge firstHalf)⟩
  symmetric := ⟨terminalSymmetry, by
    intro vertex
    have involutive : ∀ vertex : Fin 20, terminalSymmetry.vertex (terminalSymmetry.vertex vertex) = vertex := by decide
    exact involutive vertex, by decide⟩

theorem own_critical_point :
    ∃ probability : ℝ, 0 < probability ∧ probability < 1 ∧ network.reliability probability = probability :=
  classical.exists_interior_fixed_point

end
end IGSIII4.LongDiamond
