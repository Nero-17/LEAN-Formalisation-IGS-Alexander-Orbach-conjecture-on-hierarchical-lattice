import Universality.Examples.Diamond
import Universality.Graph.CyclicSimilarity
import Universality.Graph.DistanceCertificate

namespace Universality
noncomputable section
open FiniteNetwork Polynomial Matrix
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

def twoEdgePathNetwork : FiniteNetwork 3 2 where
  endpoint := ![(0, 2), (2, 1)]
  source := 0
  target := 1
  terminals_distinct := by decide
  loopless := by decide

def triangleNetwork : FiniteNetwork 3 3 where
  endpoint := ![(0, 2), (2, 1), (0, 1)]
  source := 0
  target := 1
  terminals_distinct := by decide
  loopless := by decide

def twoEdgePathRule : Rule := ⟨3, 2, twoEdgePathNetwork⟩
def triangleRule : Rule := ⟨3, 3, triangleNetwork⟩
def tieRule : Rule := twoEdgePathRule * triangleRule
def gemRule : Rule := triangleRule * twoEdgePathRule

theorem twoEdgePath_crossing_counts :
    ∀ k : Fin 3, twoEdgePathNetwork.crossingCountBySize k = ![0, 0, 1] k := by decide

theorem triangle_crossing_counts :
    ∀ k : Fin 4, triangleNetwork.crossingCountBySize k = ![0, 1, 3, 1] k := by decide

theorem twoEdgePath_reliabilityPolynomial :
    twoEdgePathNetwork.reliabilityPolynomial = X ^ 2 := by
  rw [reliabilityPolynomial_bernstein]
  have h0 : twoEdgePathNetwork.crossingCountBySize 0 = 0 := twoEdgePath_crossing_counts 0
  have h1 : twoEdgePathNetwork.crossingCountBySize 1 = 0 := twoEdgePath_crossing_counts 1
  have h2 : twoEdgePathNetwork.crossingCountBySize 2 = 1 := twoEdgePath_crossing_counts 2
  norm_num [Finset.sum_range_succ, h0, h1, h2]

theorem triangle_reliabilityPolynomial :
    triangleNetwork.reliabilityPolynomial = X + X ^ 2 - X ^ 3 := by
  rw [reliabilityPolynomial_bernstein]
  have h0 : triangleNetwork.crossingCountBySize 0 = 0 := triangle_crossing_counts 0
  have h1 : triangleNetwork.crossingCountBySize 1 = 1 := triangle_crossing_counts 1
  have h2 : triangleNetwork.crossingCountBySize 2 = 3 := triangle_crossing_counts 2
  have h3 : triangleNetwork.crossingCountBySize 3 = 1 := triangle_crossing_counts 3
  norm_num [Finset.sum_range_succ, h0, h1, h2, h3]
  ring

theorem twoEdgePath_reliability (p : ℝ) : twoEdgePathNetwork.reliability p = p ^ 2 := by
  rw [← twoEdgePathNetwork.reliabilityPolynomial_eval, twoEdgePath_reliabilityPolynomial]
  simp

theorem triangle_reliability (p : ℝ) : triangleNetwork.reliability p = p + p ^ 2 - p ^ 3 := by
  rw [← triangleNetwork.reliabilityPolynomial_eval, triangle_reliabilityPolynomial]
  simp

theorem tie_reliability (p : ℝ) : tieRule.network.reliability p = (p + p ^ 2 - p ^ 3) ^ 2 := by
  rw [tieRule, Rule.mul_reliability]
  exact (twoEdgePath_reliability _).trans (congrArg (fun x : ℝ => x ^ 2) (triangle_reliability p))

theorem gem_reliability (p : ℝ) : gemRule.network.reliability p = p ^ 2 + p ^ 4 - p ^ 6 := by
  rw [gemRule, Rule.mul_reliability]
  change triangleNetwork.reliability (twoEdgePathNetwork.reliability p) = _
  rw [triangle_reliability, twoEdgePath_reliability]
  ring

def twoEdgePathTerminalSymmetry : twoEdgePathNetwork.NetworkSymmetry where
  vertex := Equiv.swap 0 1
  edge := Equiv.swap 0 1
  endpoint := by decide

def triangleTerminalSymmetry : triangleNetwork.NetworkSymmetry where
  vertex := Equiv.swap 0 1
  edge := Equiv.swap 0 1
  endpoint := by decide

theorem twoEdgePath_terminalSymmetric : twoEdgePathRule.TerminalSymmetric :=
  ⟨twoEdgePathTerminalSymmetry, by decide, by decide⟩

theorem triangle_terminalSymmetric : triangleRule.TerminalSymmetric :=
  ⟨triangleTerminalSymmetry, by decide, by decide⟩

def twoEdgePathDistanceCertificate : twoEdgePathNetwork.DistanceCertificate where
  length := 2
  height := ![0, 2, 1]
  source_height := rfl
  target_height := rfl
  edge_bound := by decide
  walk := .cons (by decide : twoEdgePathNetwork.fullGraph.Adj 0 2)
    (.cons (by decide : twoEdgePathNetwork.fullGraph.Adj 2 1) .nil)
  walk_length := rfl

def triangleDistanceCertificate : triangleNetwork.DistanceCertificate where
  length := 1
  height := ![0, 1, 1]
  source_height := rfl
  target_height := rfl
  edge_bound := by decide
  walk := .cons (by decide : triangleNetwork.fullGraph.Adj 0 1) .nil
  walk_length := rfl

theorem twoEdgePath_connected :
    twoEdgePathNetwork.fullGraph.Reachable twoEdgePathNetwork.source twoEdgePathNetwork.target :=
  ⟨twoEdgePathDistanceCertificate.walk⟩

theorem triangle_connected :
    triangleNetwork.fullGraph.Reachable triangleNetwork.source triangleNetwork.target :=
  ⟨triangleDistanceCertificate.walk⟩

theorem tie_gem_edges : tieRule.edges = 6 ∧ gemRule.edges = 6 := by
  constructor <;> rfl

theorem tie_gem_distance :
    tieRule.network.fullGraph.dist tieRule.network.source tieRule.network.target = 2 ∧
    gemRule.network.fullGraph.dist gemRule.network.source gemRule.network.target = 2 := by
  constructor
  · change (twoEdgePathNetwork.substitute triangleNetwork).fullGraph.dist (twoEdgePathNetwork.substitute triangleNetwork).source (twoEdgePathNetwork.substitute triangleNetwork).target = 2
    rw [substitute_terminal_distance _ _ twoEdgePath_connected triangle_connected,
      twoEdgePathDistanceCertificate.distance_eq, triangleDistanceCertificate.distance_eq]
    rfl
  · change (triangleNetwork.substitute twoEdgePathNetwork).fullGraph.dist (triangleNetwork.substitute twoEdgePathNetwork).source (triangleNetwork.substitute twoEdgePathNetwork).target = 2
    rw [substitute_terminal_distance _ _ triangle_connected twoEdgePath_connected,
      twoEdgePathDistanceCertificate.distance_eq, triangleDistanceCertificate.distance_eq]
    rfl

theorem tie_gem_fixed_point (p : ℝ) (hfixed : gemRule.network.reliability p = p) :
    tieRule.network.reliability (p ^ 2) = p ^ 2 ∧ p ^ 2 + (p ^ 2) ^ 2 - (p ^ 2) ^ 3 = p := by
  constructor
  · simpa only [tieRule, gemRule, twoEdgePathRule, twoEdgePath_reliability] using
      Rule.cyclic_substitution_fixed_point triangleRule twoEdgePathRule p hfixed
  · simpa only [gemRule, Rule.mul_reliability, triangleRule, twoEdgePathRule,
      triangle_reliability, twoEdgePath_reliability] using hfixed

theorem tie_gem_response (p : ℝ) (hfixed : gemRule.network.reliability p = p) :
    deriv gemRule.network.reliability p = deriv tieRule.network.reliability (p ^ 2) := by
  simpa only [tieRule, gemRule, twoEdgePathRule, twoEdgePath_reliability] using
    Rule.cyclic_substitution_response triangleRule twoEdgePathRule p hfixed

theorem tie_gem_spectralRadius (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    spectralRadius ℂ ((gemRule.network.massMatrix p).map Complex.ofReal) =
      spectralRadius ℂ ((tieRule.network.massMatrix (p ^ 2)).map Complex.ofReal) := by
  simpa only [tieRule, gemRule, twoEdgePathRule, twoEdgePath_reliability] using
    Rule.cyclic_substitution_spectralRadius triangleRule twoEdgePathRule p hp hp'
      twoEdgePath_connected hfixed triangleTerminalSymmetry (by decide) (by decide)
      twoEdgePathTerminalSymmetry (by decide) (by decide)

end
end Universality
