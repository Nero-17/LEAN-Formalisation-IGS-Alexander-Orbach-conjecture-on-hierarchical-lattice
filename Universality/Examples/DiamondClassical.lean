import Universality.Examples.DiamondCritical
import Universality.Graph.ClassicalRule

namespace Universality
noncomputable section
open FiniteNetwork Matrix Filter
open scoped Topology

def diamondRule : Rule := ⟨4, 4, diamondNetwork⟩

def diamondTerminalSymmetry : diamondNetwork.NetworkSymmetry where
  vertex := Equiv.swap 0 1
  edge := (Equiv.swap 0 1).trans (Equiv.swap 2 3)
  endpoint := by decide

def diamondCanonicalWalk (edge : Fin 4) :
    diamondNetwork.fullGraph.Walk diamondNetwork.source diamondNetwork.target :=
  if edge.val < 2 then
    .cons (by decide : diamondNetwork.fullGraph.Adj 0 2)
      (.cons (by decide : diamondNetwork.fullGraph.Adj 2 1) .nil)
  else
    .cons (by decide : diamondNetwork.fullGraph.Adj 0 3)
      (.cons (by decide : diamondNetwork.fullGraph.Adj 3 1) .nil)

def diamondDistanceCertificate : diamondNetwork.DistanceCertificate where
  length := 2
  height := ![0, 2, 1, 1]
  source_height := rfl
  target_height := rfl
  edge_bound := by decide
  walk := diamondCanonicalWalk 0
  walk_length := rfl

theorem diamond_terminal_distance :
    diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target = 2 :=
  diamondDistanceCertificate.distance_eq

theorem diamondRule_classical : diamondRule.Classical where
  connected := by
    intro v
    apply (diamondNetwork.fullGraph.reachableDecide_eq_true diamondNetwork.source v).mp
    have h : ∀ v, diamondNetwork.fullGraph.reachableDecide diamondNetwork.source v = true := by decide
    exact h v
  simple := by decide
  canonical := by
    intro edge
    refine ⟨diamondCanonicalWalk edge, ?_, ?_⟩
    · apply SimpleGraph.Walk.IsPath.mk'
      fin_cases edge <;> decide
    · fin_cases edge <;> decide
  scale := by
    change 1 < diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target
    rw [diamond_terminal_distance]
    norm_num
  cut := by decide
  symmetric := ⟨diamondTerminalSymmetry,
    by intro v; fin_cases v <;> decide, by decide⟩

theorem diamond_critical_block_positive :
    ∀ i j, 0 < massPlaneBlock (diamondNetwork.massMatrix diamondCriticalProbability) i j := by
  rw [diamond_critical_block]
  intro i j
  have hp := diamond_critical_probability_bounds.1
  fin_cases i <;> fin_cases j <;> simp <;> positivity

theorem diamond_critical_positiveRoot :
    positiveRoot (massPlaneBlock (diamondNetwork.massMatrix diamondCriticalProbability)) =
      7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5) := by
  have hdisc :
      (massPlaneBlock (diamondNetwork.massMatrix diamondCriticalProbability) 0 0 -
        massPlaneBlock (diamondNetwork.massMatrix diamondCriticalProbability) 1 1) ^ 2 +
      4 * massPlaneBlock (diamondNetwork.massMatrix diamondCriticalProbability) 0 1 *
        massPlaneBlock (diamondNetwork.massMatrix diamondCriticalProbability) 1 0 =
      4 * (73 - 32 * Real.sqrt 5) := by
    have htrace := diamond_critical_block_trace
    have hdet := diamond_critical_block_det
    rw [Matrix.trace_fin_two] at htrace
    rw [Matrix.det_fin_two] at hdet
    have htrace₂ := congrArg (fun x : ℝ => x ^ 2) htrace
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
  have hfour : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
  rw [positiveRoot, hdisc, Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num)]
  rw [← Matrix.trace_fin_two, diamond_critical_block_trace]
  rw [hfour]
  ring

theorem diamond_critical_spectralRadius :
    spectralRadius ℂ ((diamondNetwork.massMatrix diamondCriticalProbability).map Complex.ofReal) =
      ENNReal.ofReal (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) := by
  rw [← diamond_critical_positiveRoot]
  apply massPlane_spectralRadius
  · exact diamondNetwork.massMatrix_nonneg diamond_critical_probability_bounds.1.le
      diamond_critical_probability_bounds.2.le
  · exact diamondNetwork.massMatrix_preservesMassPlane _ diamondTerminalSymmetry
      (by decide) (by decide)
  · exact diamond_critical_block_positive

theorem diamond_critical_secondaryRoot :
    secondaryRoot (massPlaneBlock (diamondNetwork.massMatrix diamondCriticalProbability)) =
      7 - 2 * Real.sqrt 5 - Real.sqrt (73 - 32 * Real.sqrt 5) := by
  rw [secondaryRoot, diamond_critical_block_trace, diamond_critical_positiveRoot]
  ring

theorem diamond_pivotal_dimension :
    Tendsto (diamondRule.pivotalLogarithmicGrowth diamondCriticalProbability) atTop
      (𝓝 (Real.log (6 - 2 * Real.sqrt 5) / Real.log 2)) := by
  have h := diamondRule_classical.pivotal_dimension diamondCriticalProbability
    diamond_critical_probability_bounds.1 diamond_critical_probability_bounds.2 diamond_critical_fixed_point
  change Tendsto _ _ (𝓝 (Real.log (deriv diamondNetwork.reliability diamondCriticalProbability) /
    Real.log (diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target))) at h
  simpa only [diamond_critical_response, diamond_terminal_distance, Nat.cast_ofNat] using h

theorem diamond_mass_dimension :
    Tendsto (fun n : ℕ =>
      Real.log ((diamondRule.generation n).network.conditionalClusterMass diamondCriticalProbability .connected) /
      Real.log ((diamondRule.generation n).network.fullGraph.dist
        (diamondRule.generation n).network.source (diamondRule.generation n).network.target)) atTop
      (𝓝 (Real.log (7 - 2 * Real.sqrt 5 + Real.sqrt (73 - 32 * Real.sqrt 5)) / Real.log 2)) := by
  have h := diamondRule_classical.mass_dimension diamondCriticalProbability
    diamond_critical_probability_bounds.1 diamond_critical_probability_bounds.2 diamond_critical_fixed_point .connected
  have hr := (positiveRoot_pos _ diamond_critical_block_positive).le
  rw [diamond_critical_positiveRoot] at hr
  change Tendsto _ _ (𝓝 (Real.log ((spectralRadius ℂ
    ((diamondNetwork.massMatrix diamondCriticalProbability).map Complex.ofReal)).toReal) /
    Real.log (diamondNetwork.fullGraph.dist diamondNetwork.source diamondNetwork.target))) at h
  simpa only [diamond_critical_spectralRadius, ENNReal.toReal_ofReal hr,
    diamond_terminal_distance, Nat.cast_ofNat] using h

end
end Universality
