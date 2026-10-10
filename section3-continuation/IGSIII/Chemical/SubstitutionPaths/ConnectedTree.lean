import IGSIII.Chemical.SubstitutionPaths.InnovationTree

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Identification with the existing common-tree chemical functional

Bond addresses are the alphabet used by `terminalDistance`. Actual cells are
extracted by their indexed edge and reassociated explicitly. At a noncrossing
address the connected completion copies the connected root configuration.
This is only a deterministic completion of unused coordinates: no independence
or product-law assertion is made about these copied coordinates.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

noncomputable def configurationBondChildSequence (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (bond : Sym2 (Fin rule.vertices)) :
    (depth : ℕ) → Configuration (rule.generation depth).edges := by
  classical
  exact if represented : ∃ edge, s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2) = bond
    then configurationChildSequence rule configuration represented.choose else configuration

theorem configurationBondChildSequence_endpoint (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (edge : Fin rule.edges) :
    configurationBondChildSequence rule configuration
        s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2) =
      configurationChildSequence rule configuration edge := by
  classical
  have represented : ∃ child, s((rule.network.endpoint child).1, (rule.network.endpoint child).2) =
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2) := ⟨edge, rfl⟩
  simp only [configurationBondChildSequence, dif_pos represented]
  rw [simple represented.choose_spec]

theorem configurationBondChildSequence_coherent (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (bond : Sym2 (Fin rule.vertices)) :
    configurationSequenceCoherent rule (configurationBondChildSequence rule configuration bond) := by
  classical
  unfold configurationBondChildSequence
  split
  · exact configurationChildSequence_coherent rule configuration coherent _
  · exact coherent

noncomputable def configurationBondTree (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges) :
    List (Sym2 (Fin rule.vertices)) → (depth : ℕ) → Configuration (rule.generation depth).edges
  | [] => configuration
  | bond :: address => configurationBondTree rule
      (configurationBondChildSequence rule configuration bond) address

theorem configurationBondTree_append (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (address continuation : List (Sym2 (Fin rule.vertices))) :
    configurationBondTree rule configuration (address ++ continuation) =
      configurationBondTree rule (configurationBondTree rule configuration address) continuation := by
  induction address generalizing configuration with
  | nil => rfl
  | cons bond address inductionHypothesis =>
      exact inductionHypothesis (configurationBondChildSequence rule configuration bond)

theorem configurationBondTree_child (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (address : List (Sym2 (Fin rule.vertices))) (edge : Fin rule.edges) (depth : ℕ) :
    configurationBondTree rule configuration
        (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]) depth =
      generationTopCells rule depth (configurationBondTree rule configuration address (depth + 1)) edge := by
  rw [configurationBondTree_append]
  change configurationBondChildSequence rule (configurationBondTree rule configuration address)
    s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2) depth = _
  rw [configurationBondChildSequence_endpoint rule simple]
  rfl

theorem configurationBondTree_coherent (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (address : List (Sym2 (Fin rule.vertices))) :
    configurationSequenceCoherent rule (configurationBondTree rule configuration address) := by
  induction address generalizing configuration with
  | nil => exact coherent
  | cons bond address inductionHypothesis =>
      exact inductionHypothesis (configurationBondChildSequence rule configuration bond)
        (configurationBondChildSequence_coherent rule configuration coherent bond)

theorem configurationBondTree_root (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (address : List (Sym2 (Fin rule.vertices))) (depth : ℕ) :
    generationRootConfiguration rule depth
        (configurationBondTree rule configuration address (depth + 1)) =
      configurationBondTree rule configuration address 0 :=
  configurationSequence_root rule _ (configurationBondTree_coherent rule configuration coherent address) depth

theorem configurationBondTree_child_crosses (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (address : List (Sym2 (Fin rule.vertices))) (edge : Fin rule.edges) :
    rule.network.crosses (configurationBondTree rule configuration
        (address ++ [s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)]) 0) =
      configurationBondTree rule configuration address 0 edge := by
  rw [configurationBondTree_child rule simple]
  change generationRootConfiguration rule 0
    (configurationBondTree rule configuration address 1) edge = _
  rw [configurationBondTree_root rule configuration coherent]

noncomputable def connectedCompletion (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (address : List (Sym2 (Fin rule.vertices))) : Configuration rule.edges :=
  if rule.network.crosses (configurationBondTree rule configuration address 0) then
    configurationBondTree rule configuration address 0 else configuration 0

theorem connectedCompletion_eq (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (address : List (Sym2 (Fin rule.vertices)))
    (crossing : rule.network.crosses (configurationBondTree rule configuration address 0) = true) :
    connectedCompletion rule configuration address = configurationBondTree rule configuration address 0 := by
  simp only [connectedCompletion, crossing, if_true]

theorem connectedCompletion_crosses (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (rootCrossing : rule.network.crosses (configuration 0) = true)
    (address : List (Sym2 (Fin rule.vertices))) :
    rule.network.crosses (connectedCompletion rule configuration address) = true := by
  unfold connectedCompletion
  split
  · assumption
  · exact rootCrossing

/-- The existing `terminalDistance` is the actual graph distance at every
connected address of the coherent configuration tree. -/
theorem configurationBondTree_distance_eq_terminalDistance (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (rootCrossing : rule.network.crosses (configuration 0) = true)
    (depth : ℕ) (address : List (Sym2 (Fin rule.vertices)))
    (crossing : rule.network.crosses (configurationBondTree rule configuration address 0) = true) :
    (((rule.generation depth).network.openGraph
        (configurationBondTree rule configuration address depth)).dist
          (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) =
      terminalDistance (innovationPathFamily rule (connectedCompletion rule configuration)
        (connectedCompletion_crosses rule configuration rootCrossing)) address (depth + 1) := by
  induction depth generalizing address with
  | zero =>
      rw [terminalDistance_succ]
      simp only [terminalDistance_zero, innovationPathFamily,
        connectedCompletion_eq rule configuration address crossing]
      exact (graphPathFamily_shortest_unit _ _ _ ((rule.network.crosses_eq_true _).mp crossing)).symm
  | succ depth inductionHypothesis =>
      have root := configurationBondTree_root rule configuration coherent address depth
      have reachable : (rule.network.openGraph (configurationBondTree rule configuration address 0)).Reachable
          rule.network.source rule.network.target := (rule.network.crosses_eq_true _).mp crossing
      rw [generation_distance_eq_cellMinPlus rule simple, root, cellMinPlus,
        weightedDistance_of_reachable _ _ reachable, terminalDistance_succ]
      simp only [innovationPathFamily, connectedCompletion_eq rule configuration address crossing]
      apply shortest_congr_used
      intro path membership bond edgeMembership
      obtain ⟨edge, retained, rfl⟩ := graphPathFamily_used_edge rule.network
        (configurationBondTree rule configuration address 0) reachable membership edgeMembership
      rw [childDistanceCost_endpoint rule.network (rule.generation depth).network _ simple edge]
      rw [← configurationBondTree_child rule simple]
      exact inductionHypothesis _
        ((configurationBondTree_child_crosses rule simple configuration coherent address edge).trans retained)

/-- The scalar chemical recursion is identified on the original conditioned
configuration-history probability space, simultaneously in refinement depth. -/
theorem actual_history_distance_eq_terminalDistance (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive lessOne fixedPoint true,
      ∃ crossing : rule.network.crosses (actualConfigurationSequence rule path 0) = true,
        ∀ depth, (((rule.generation depth).network.openGraph
            (Rule.ConfigurationHistory.latest rule depth (path depth))).dist
              (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) =
          terminalDistance (innovationPathFamily rule
            (connectedCompletion rule (actualConfigurationSequence rule path))
            (connectedCompletion_crosses rule (actualConfigurationSequence rule path) crossing)) [] (depth + 1) := by
  filter_upwards [Rule.ConfigurationHistory.infiniteLaw_coarsens rule p positive lessOne fixedPoint true,
    infinite_history_latest_crosses rule p positive lessOne fixedPoint true] with path coherent crossing
  refine ⟨crossing 0, ?_⟩
  intro depth
  exact configurationBondTree_distance_eq_terminalDistance rule simple (actualConfigurationSequence rule path)
    coherent (crossing 0) depth [] (crossing 0)

end IGSIII.Chemical.Substitution
