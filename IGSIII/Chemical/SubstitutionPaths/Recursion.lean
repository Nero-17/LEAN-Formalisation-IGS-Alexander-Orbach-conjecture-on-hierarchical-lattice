import IGSIII.Chemical.SubstitutionPaths.Network
import IGSIII.Chemical.Recursion

set_option autoImplicit false

/-!
# Actual finite graphs realizing the chemical recursion

A fixed finite rule is placed at every address. Each address carries a
terminal-connected retained-edge configuration. An absent edge deletes its
entire descendant cell; a retained edge carries the child's actual finite
graph. The graph at index zero is the first rule graph, so its chemical depth
is one. The terminal-distance theorem identifies these genuine recursively
substituted finite graphs with `terminalDistance`, rather than assuming that
identity as structural data.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

theorem closed_openGraph {vertices edges : ℕ} (network : FiniteNetwork vertices edges) :
    network.openGraph (fun _ => false) = ⊥ := by
  ext first second
  simp [FiniteNetwork.openGraph]

theorem closed_not_crosses {vertices edges : ℕ} (network : FiniteNetwork vertices edges) :
    network.crosses (fun _ => false) = false := by
  apply Bool.eq_false_iff.mpr
  intro crossing
  have reachable := (network.crosses_eq_true _).mp crossing
  rw [closed_openGraph, SimpleGraph.reachable_bot] at reachable
  exact network.terminals_distinct reachable

theorem masked_coarse_configuration {outerEdges vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (retained : Configuration outerEdges)
    (configuration : Fin outerEdges → Configuration edges)
    (crossing : ∀ edge, network.crosses (configuration edge) = true) :
    network.coarseConfiguration (fun edge child => retained edge && configuration edge child) =
      retained := by
  funext edge
  change network.crosses (fun child => retained edge && configuration edge child) = retained edge
  cases retention : retained edge with
  | false => simpa only [retention, Bool.false_and] using closed_not_crosses network
  | true => simpa only [retention, Bool.true_and] using crossing edge

/-- Top-down finite substitution. The first rule graph has index zero. -/
noncomputable def recursiveRule (rule : Rule) : ℕ → Rule
  | 0 => rule
  | depth + 1 => rule * recursiveRule rule depth

/-- Percolation on the actual finite network, with absent parent edges deleting
all their descendants. -/
noncomputable def descendantConfiguration (rule : Rule)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges) :
    (depth : ℕ) → List (Sym2 (Fin rule.vertices)) → Configuration (recursiveRule rule depth).edges
  | 0, address => innovation address
  | depth + 1, address => substitutionConfigurationEquiv
      (fun edge child => innovation address edge &&
        descendantConfiguration rule innovation depth
          (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]) child)

noncomputable def descendantChildren (rule : Rule)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    Fin rule.edges → Configuration (recursiveRule rule depth).edges :=
  fun edge child => innovation address edge && descendantConfiguration rule innovation depth
    (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]) child

@[simp] theorem descendantConfiguration_succ (rule : Rule)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    descendantConfiguration rule innovation (depth + 1) address =
      substitutionConfigurationEquiv (descendantChildren rule innovation depth address) := rfl

theorem descendant_crosses (rule : Rule)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (crossing : ∀ address, rule.network.crosses (innovation address) = true)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    (recursiveRule rule depth).network.crosses
      (descendantConfiguration rule innovation depth address) = true := by
  induction depth generalizing address with
  | zero => exact crossing address
  | succ depth inductionHypothesis =>
      change (rule.network.substitute (recursiveRule rule depth).network).crosses
        (substitutionConfigurationEquiv (descendantChildren rule innovation depth address)) = true
      rw [substitute_crosses]
      have coarse := masked_coarse_configuration (recursiveRule rule depth).network
        (innovation address)
        (fun edge => descendantConfiguration rule innovation depth
          (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]))
        (fun edge => inductionHypothesis
          (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]))
      rw [show (recursiveRule rule depth).network.coarseConfiguration
        (descendantChildren rule innovation depth address) = innovation address from coarse]
      exact crossing address

theorem descendant_coarse_configuration (rule : Rule)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (crossing : ∀ address, rule.network.crosses (innovation address) = true)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    (recursiveRule rule depth).network.coarseConfiguration
        (descendantChildren rule innovation depth address) = innovation address :=
  masked_coarse_configuration (recursiveRule rule depth).network (innovation address)
    (fun edge => descendantConfiguration rule innovation depth
      (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]))
    (fun edge => descendant_crosses rule innovation crossing depth
      (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]))

noncomputable def innovationPathFamily (rule : Rule)
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (crossing : ∀ address, rule.network.crosses (innovation address) = true)
    (address : List (Sym2 (Fin rule.vertices))) : PathFamily (Sym2 (Fin rule.vertices)) :=
  graphPathFamily (rule.network.openGraph (innovation address)) rule.network.source rule.network.target
    ((rule.network.crosses_eq_true _).mp (crossing address))

theorem shortest_congr_used {Edge : Type*} [DecidableEq Edge] (family : PathFamily Edge)
    {first second : Edge → ℝ}
    (comparison : ∀ path ∈ family.paths, ∀ edge ∈ path, first edge = second edge) :
    family.shortest first = family.shortest second := by
  have pathCosts : ∀ path ∈ family.paths,
      PathFamily.pathCost path first = PathFamily.pathCost path second := by
    intro path membership
    exact Finset.sum_congr rfl (fun edge edgeMembership => comparison path membership edge edgeMembership)
  apply le_antisymm
  · apply family.le_shortest
    intro path membership
    rw [← pathCosts path membership]
    exact family.shortest_le_pathCost first membership
  · apply family.le_shortest
    intro path membership
    rw [pathCosts path membership]
    exact family.shortest_le_pathCost second membership

theorem graphPathFamily_used_edge {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (reachable : (network.openGraph configuration).Reachable network.source network.target)
    {path : Finset (Sym2 (Fin vertices))}
    (membership : path ∈ (graphPathFamily (network.openGraph configuration)
      network.source network.target reachable).paths)
    {bond : Sym2 (Fin vertices)} (edgeMembership : bond ∈ path) :
    ∃ edge, configuration edge = true ∧
      bond = s((network.endpoint edge).1, (network.endpoint edge).2) := by
  obtain ⟨walk, _, rfl⟩ :=
    (mem_graphPathFamily _ network.source network.target reachable path).mp membership
  revert edgeMembership
  refine Sym2.inductionOn bond (fun first second edgeMembership => ?_)
  obtain ⟨_, edge, retained, endpoints | endpoints⟩ :=
    walk.adj_of_mem_edges (List.mem_toFinset.mp edgeMembership)
  · exact ⟨edge, retained, by rw [endpoints]⟩
  · exact ⟨edge, retained, by rw [endpoints, Sym2.eq_swap]⟩

/-- The finite graph at every depth realizes the deterministic chemical
recursion. Terminal-connected innovations and simplicity of the fixed outer
rule are the only hypotheses. -/
theorem descendant_distance_eq_terminalDistance (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (innovation : List (Sym2 (Fin rule.vertices)) → Configuration rule.edges)
    (crossing : ∀ address, rule.network.crosses (innovation address) = true)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices))) :
    (((recursiveRule rule depth).network.openGraph
        (descendantConfiguration rule innovation depth address)).dist
          (recursiveRule rule depth).network.source
          (recursiveRule rule depth).network.target : ℝ) =
      terminalDistance (innovationPathFamily rule innovation crossing) address (depth + 1) := by
  induction depth generalizing address with
  | zero =>
      change ((rule.network.openGraph (innovation address)).dist
          rule.network.source rule.network.target : ℝ) =
        terminalDistance (innovationPathFamily rule innovation crossing) address (0 + 1)
      rw [terminalDistance_succ]
      simp only [terminalDistance_zero]
      exact (graphPathFamily_shortest_unit _ _ _
        ((rule.network.crosses_eq_true _).mp (crossing address))).symm
  | succ depth inductionHypothesis =>
      have coarse := descendant_coarse_configuration rule innovation crossing depth address
      have reachable : (rule.network.openGraph
          ((recursiveRule rule depth).network.coarseConfiguration
            (descendantChildren rule innovation depth address))).Reachable
          rule.network.source rule.network.target := by
        rw [coarse]
        exact (rule.network.crosses_eq_true _).mp (crossing address)
      have oneStep := substitute_terminal_distance_eq_shortest rule.network
        (recursiveRule rule depth).network (descendantChildren rule innovation depth address)
        simple reachable
      simp only [coarse] at oneStep
      change (((rule.network.substitute (recursiveRule rule depth).network).openGraph
          (substitutionConfigurationEquiv (descendantChildren rule innovation depth address))).dist
            (rule.network.substitute (recursiveRule rule depth).network).source
            (rule.network.substitute (recursiveRule rule depth).network).target : ℝ) = _
      rw [oneStep, terminalDistance_succ]
      change (innovationPathFamily rule innovation crossing address).shortest _ =
        (innovationPathFamily rule innovation crossing address).shortest _
      apply shortest_congr_used
      intro path membership bond edgeMembership
      obtain ⟨edge, retained, rfl⟩ := graphPathFamily_used_edge rule.network (innovation address)
        ((rule.network.crosses_eq_true _).mp (crossing address)) membership edgeMembership
      rw [childDistanceCost_endpoint rule.network (recursiveRule rule depth).network
        (descendantChildren rule innovation depth address) simple edge]
      have childConfiguration : descendantChildren rule innovation depth address edge =
          descendantConfiguration rule innovation depth
            (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]) := by
        funext child
        simp only [descendantChildren, retained, Bool.true_and]
      rw [childConfiguration]
      exact inductionHypothesis
        (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)])

end IGSIII.Chemical.Substitution
