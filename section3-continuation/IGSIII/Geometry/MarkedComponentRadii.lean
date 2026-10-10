import IGSIII.Geometry.ActualComponentRadius
import IGSIII.Mass.CylinderCounts

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open scoped BigOperators

/-- Actual terminal-component radii on the original common innovation tree. -/
noncomputable def markedTerminalComponentRadius (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) : ℕ :=
  terminalComponentRadius (rule.generation depth).network
    (markedGenerationConfiguration rule marks depth address opened)

noncomputable def markedTerminalDistance (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) : ℕ :=
  ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth address opened)).dist
    (rule.generation depth).network.source (rule.generation depth).network.target

/-- The actual radius recursion simultaneously covers connected components,
both noncrossing sides, and every one-terminal mask. -/
theorem markedTerminalComponentRadius_succ_le (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) (opened : Bool) :
    markedTerminalComponentRadius rule marks (depth + 1) address opened ≤
      (Finset.univ.sup (fun edge => markedTerminalComponentRadius rule marks depth
        (address ++ [edge]) (marks (address, opened) edge))) +
      rule.edges * (Finset.univ.sup (fun edge => markedTerminalDistance rule marks depth
        (address ++ [edge]) (marks (address, opened) edge))) := by
  unfold markedTerminalComponentRadius
  rw [← terminalComponentRadius_equivalence (rule.generationTopDecomposition depth)]
  simp only [markedGenerationConfiguration, Equiv.apply_symm_apply]
  apply terminalComponentRadius_substitute_le
  · intro edge
    exact Finset.le_sup (f := fun edge => terminalComponentRadius (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth (address ++ [edge]) (marks (address, opened) edge)))
        (Finset.mem_univ edge)
  · intro edge _
    exact Finset.le_sup (f := fun edge => markedTerminalDistance rule marks depth
      (address ++ [edge]) (marks (address, opened) edge)) (Finset.mem_univ edge)

theorem markedTerminalComponentRadius_zero_le (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges)) (opened : Bool) :
    markedTerminalComponentRadius rule marks 0 address opened ≤ rule.edges := by
  apply terminalComponentRadius_le
  · intro vertex
    by_cases reachable : (rule.network.openGraph (marks (address, opened))).Reachable rule.network.source vertex
    · exact openGraph_distance_le_edges rule.network _ reachable
    · exact (SimpleGraph.dist_eq_zero_of_not_reachable reachable).le.trans (Nat.zero_le _)
  · intro vertex
    by_cases reachable : (rule.network.openGraph (marks (address, opened))).Reachable rule.network.target vertex
    · exact openGraph_distance_le_edges rule.network _ reachable
    · exact (SimpleGraph.dist_eq_zero_of_not_reachable reachable).le.trans (Nat.zero_le _)

/-- Noncrossing marks contribute no terminal through-distance. The same raw
noncrossing configuration is retained for both sides and their descendants. -/
theorem markedTerminalDistance_noncrossing (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    markedTerminalDistance rule marks depth address false = 0 := by
  apply SimpleGraph.dist_eq_zero_of_not_reachable
  intro reachable
  have terminal_crossing := ((rule.generation depth).network.crosses_eq_true _).mpr reachable
  rw [markedGenerationConfiguration_crosses rule marks crossing] at terminal_crossing
  contradiction

end IGSIII.Geometry
