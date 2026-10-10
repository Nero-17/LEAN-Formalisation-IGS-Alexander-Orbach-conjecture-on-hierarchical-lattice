import IGSIII.Chemical.FiveCycle
import IGSIII.Chemical.SubstitutionPaths.MinimalPaths
import Universality.Graph.ClassicalRule
import Universality.Percolation.CountingPolynomials
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace IGSIII.Chemical.FiveCycle

open Universality Universality.FiniteNetwork Substitution Polynomial
open scoped BigOperators

noncomputable section

def network : FiniteNetwork 5 5 where
  endpoint := ![(0, 2), (2, 1), (0, 3), (3, 4), (4, 1)]
  source := 0
  target := 1
  terminals_distinct := by decide
  loopless := by decide

def rule : Rule := ⟨5, 5, network⟩

def shortWalk : network.fullGraph.Walk network.source network.target :=
  .cons (by decide : network.fullGraph.Adj 0 2)
    (.cons (by decide : network.fullGraph.Adj 2 1) .nil)

def longWalk : network.fullGraph.Walk network.source network.target :=
  .cons (by decide : network.fullGraph.Adj 0 3)
    (.cons (by decide : network.fullGraph.Adj 3 4)
      (.cons (by decide : network.fullGraph.Adj 4 1) .nil))

def terminalSymmetry : network.NetworkSymmetry where
  vertex := (Equiv.swap 0 1).trans (Equiv.swap 3 4)
  edge := (Equiv.swap 0 1).trans (Equiv.swap 2 4)
  endpoint := by decide

def distanceCertificate : network.DistanceCertificate where
  length := 2
  height := ![0, 2, 1, 1, 1]
  source_height := rfl
  target_height := rfl
  edge_bound := by decide
  walk := shortWalk
  walk_length := rfl

theorem terminal_distance : network.fullGraph.dist network.source network.target = 2 :=
  distanceCertificate.distance_eq

theorem rule_classical : rule.Classical where
  connected := by
    intro vertex
    apply (network.fullGraph.reachableDecide_eq_true network.source vertex).mp
    have connected : ∀ vertex, network.fullGraph.reachableDecide network.source vertex = true := by decide
    exact connected vertex
  simple := by decide
  canonical := by
    intro edge
    by_cases short : edge.val < 2
    · refine ⟨shortWalk, ?_, ?_⟩
      · apply SimpleGraph.Walk.IsPath.mk'; decide
      · fin_cases edge <;> simp_all <;> decide
    · refine ⟨longWalk, ?_, ?_⟩
      · apply SimpleGraph.Walk.IsPath.mk'; decide
      · fin_cases edge <;> simp_all <;> decide
  scale := by
    change 1 < network.fullGraph.dist network.source network.target
    rw [terminal_distance]
    norm_num
  cut := by decide
  symmetric := ⟨terminalSymmetry, by intro vertex; fin_cases vertex <;> decide, by decide⟩

theorem crosses_iff_branches (configuration : Configuration 5) :
    network.crosses configuration =
      ((configuration 0 && configuration 1) ||
        (configuration 2 && configuration 3 && configuration 4)) := by
  have identity : ∀ configuration : Configuration 5, network.crosses configuration =
      ((configuration 0 && configuration 1) ||
        (configuration 2 && configuration 3 && configuration 4)) := by decide
  exact identity configuration

theorem exact_crossing_counts :
    ∀ count : Fin 6, network.crossingCountBySize count = ![0, 0, 1, 4, 5, 1] count := by decide

theorem actual_reliability_polynomial : network.reliabilityPolynomial = X ^ 2 + X ^ 3 - X ^ 5 := by
  rw [reliabilityPolynomial_bernstein]
  have zero : network.crossingCountBySize 0 = 0 := exact_crossing_counts 0
  have one : network.crossingCountBySize 1 = 0 := exact_crossing_counts 1
  have two : network.crossingCountBySize 2 = 1 := exact_crossing_counts 2
  have three : network.crossingCountBySize 3 = 4 := exact_crossing_counts 3
  have four : network.crossingCountBySize 4 = 5 := exact_crossing_counts 4
  have five : network.crossingCountBySize 5 = 1 := exact_crossing_counts 5
  norm_num [Finset.sum_range_succ, zero, one, two, three, four, five]
  ring

theorem actual_reliability (p : ℝ) : network.reliability p = p ^ 2 + p ^ 3 - p ^ 5 := by
  rw [← network.reliabilityPolynomial_eval, actual_reliability_polynomial]
  simp

theorem actual_fixedPoint_iff {p : ℝ} (positive : 0 < p) (lessOne : p < 1) :
    network.reliability p = p ↔ p ^ 3 + p ^ 2 = 1 := by
  rw [actual_reliability]
  exact nonendpoint_fixedPoint_iff positive.ne' (ne_of_lt lessOne)

theorem minimal_path_iff_branches (path : Finset (Fin 5)) :
    MinimalCrossingConfiguration network (configurationOfPath path) ↔
      path = {0, 1} ∨ path = {2, 3, 4} := by
  have classification : ∀ path : Finset (Fin 5),
      MinimalCrossingConfiguration network (fun edge => decide (edge ∈ path)) ↔
        path = {0, 1} ∨ path = {2, 3, 4} := by
    unfold MinimalCrossingConfiguration
    decide
  exact classification path

theorem actual_path_iff_branches (configuration : Configuration 5)
    (crossing : network.crosses configuration = true) (path : Finset (Fin 5)) :
    path ∈ (edgePathFamily network configuration).paths ↔
      (path = {0, 1} ∨ path = {2, 3, 4}) ∧ ∀ edge ∈ path, configuration edge = true := by
  rw [edgePathFamily_mem_iff_minimal network rule_classical.simple configuration crossing,
    minimal_path_iff_branches]

end
end IGSIII.Chemical.FiveCycle
