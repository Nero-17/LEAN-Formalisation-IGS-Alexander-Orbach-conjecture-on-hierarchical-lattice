import IGSIII.Chemical.SubstitutionPaths.CoherentHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# A common configuration tree extracted from the actual infinite history

Every cell at every address is obtained from the original finest
configurations by explicit reassociation. Coarsening compatibility makes its
root innovation independent of the chosen refinement depth. The resulting
tree retains actual noncrossing cells and dangling components. Conditional
independence is expressed separately by the full configuration disintegration
in `ConditionalLaw`; it is not an assumption in this construction.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

def configurationSequenceCoherent (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges) : Prop :=
  ∀ depth, rule.coarsenGeneration depth (configuration (depth + 1)) = configuration depth

noncomputable def configurationChildSequence (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (edge : Fin rule.edges) : (depth : ℕ) → Configuration (rule.generation depth).edges :=
  fun depth => generationTopCells rule depth (configuration (depth + 1)) edge

theorem configurationChildSequence_coherent (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (edge : Fin rule.edges) :
    configurationSequenceCoherent rule (configurationChildSequence rule configuration edge) := by
  intro depth
  change rule.coarsenGeneration depth
      (generationTopCells rule (depth + 1) (configuration (depth + 2)) edge) =
    generationTopCells rule depth (configuration (depth + 1)) edge
  rw [← generationTopCells_coarsen, coherent (depth + 1)]

theorem configurationSequence_root (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (depth : ℕ) :
    generationRootConfiguration rule depth (configuration (depth + 1)) = configuration 0 := by
  induction depth with
  | zero => exact coherent 0
  | succ depth inductionHypothesis =>
      rw [generationRootConfiguration_coarsen, coherent (depth + 1)]
      exact inductionHypothesis

theorem configurationSequence_crosses (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (depth : ℕ) :
    (rule.generation depth).network.crosses (configuration depth) =
      rule.network.crosses (configuration 0) := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [generation_crosses_coarsen, coherent depth]
      exact inductionHypothesis

/-- Addresses are ordered indexed edges, matching the existing generation's
edge indices, and each descendant uses the same infinite sample. -/
noncomputable def configurationTree (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges) :
    List (Fin rule.edges) → (depth : ℕ) → Configuration (rule.generation depth).edges
  | [] => configuration
  | edge :: address => configurationTree rule (configurationChildSequence rule configuration edge) address

theorem configurationTree_append (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (address continuation : List (Fin rule.edges)) :
    configurationTree rule configuration (address ++ continuation) =
      configurationTree rule (configurationTree rule configuration address) continuation := by
  induction address generalizing configuration with
  | nil => rfl
  | cons edge address inductionHypothesis =>
      exact inductionHypothesis (configurationChildSequence rule configuration edge)

theorem configurationTree_child (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (address : List (Fin rule.edges)) (edge : Fin rule.edges) (depth : ℕ) :
    configurationTree rule configuration (address ++ [edge]) depth =
      generationTopCells rule depth (configurationTree rule configuration address (depth + 1)) edge := by
  rw [configurationTree_append]
  rfl

theorem configurationTree_coherent (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (address : List (Fin rule.edges)) :
    configurationSequenceCoherent rule (configurationTree rule configuration address) := by
  induction address generalizing configuration with
  | nil => exact coherent
  | cons edge address inductionHypothesis =>
      exact inductionHypothesis (configurationChildSequence rule configuration edge)
        (configurationChildSequence_coherent rule configuration coherent edge)

noncomputable def configurationInnovation (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (address : List (Fin rule.edges)) : Configuration rule.edges :=
  configurationTree rule configuration address 0

theorem configurationTree_root (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (address : List (Fin rule.edges)) (depth : ℕ) :
    generationRootConfiguration rule depth
        (configurationTree rule configuration address (depth + 1)) =
      configurationInnovation rule configuration address :=
  configurationSequence_root rule _ (configurationTree_coherent rule configuration coherent address) depth

theorem configurationTree_child_crosses (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (address : List (Fin rule.edges)) (edge : Fin rule.edges) (depth : ℕ) :
    (rule.generation depth).network.crosses
        (configurationTree rule configuration (address ++ [edge]) depth) =
      configurationInnovation rule configuration address edge := by
  rw [configurationTree_child]
  change generationRootConfiguration rule depth
    (configurationTree rule configuration address (depth + 1)) edge = _
  rw [configurationTree_root rule configuration coherent]

theorem configurationInnovation_child_crosses (rule : Rule)
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (address : List (Fin rule.edges)) (edge : Fin rule.edges) :
    rule.network.crosses (configurationInnovation rule configuration (address ++ [edge])) =
      configurationInnovation rule configuration address edge :=
  configurationTree_child_crosses rule configuration coherent address edge 0

/-- The min-plus recursion holds simultaneously on the actual common tree.
Disconnected child cells remain present in the configurations. -/
theorem configurationTree_distance_recursion (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (configuration : (depth : ℕ) → Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration)
    (address : List (Fin rule.edges)) (depth : ℕ) :
    (((rule.generation (depth + 1)).network.openGraph
        (configurationTree rule configuration address (depth + 1))).dist
          (rule.generation (depth + 1)).network.source
          (rule.generation (depth + 1)).network.target : ℝ) =
      cellMinPlus rule.network (rule.generation depth).network
        (configurationInnovation rule configuration address)
        (fun edge => configurationTree rule configuration (address ++ [edge]) depth) := by
  rw [generation_distance_eq_cellMinPlus rule simple,
    configurationTree_root rule configuration coherent]
  congr 1
  funext edge
  exact (configurationTree_child rule configuration address edge depth).symm

noncomputable def actualConfigurationSequence (rule : Rule)
    (path : (depth : ℕ) → rule.ConfigurationHistory depth) :
    (depth : ℕ) → Configuration (rule.generation depth).edges :=
  fun depth => Rule.ConfigurationHistory.latest rule depth (path depth)

theorem actualConfigurationSequence_child (rule : Rule)
    (path : (depth : ℕ) → rule.ConfigurationHistory depth) (edge : Fin rule.edges) :
    actualConfigurationSequence rule
        (fun depth => historyChildHistory rule depth (path (depth + 1)) edge) =
      configurationChildSequence rule (actualConfigurationSequence rule path) edge := by
  funext depth
  rw [actualConfigurationSequence, historyChildHistory_latest]
  rfl

/-- The root innovation is exactly the original initial configuration,
with its established stationary conditioned Bernoulli law. -/
theorem actual_configuration_innovation_root_atom (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) (opened : Bool)
    (coarse : Configuration rule.edges) :
    Rule.ConfigurationHistory.infiniteLaw rule p positive lessOne fixedPoint opened
        {path | configurationInnovation rule (actualConfigurationSequence rule path) [] = coarse} =
      ENNReal.ofReal (rule.network.conditionalCellWeight p opened coarse) := by
  simpa only [configurationInnovation, configurationTree, actualConfigurationSequence,
    Rule.ConfigurationHistory.latest, Rule.ConfigurationHistory.recursiveWeight] using
      Rule.ConfigurationHistory.infiniteLaw_history_atom rule p positive lessOne fixedPoint opened 0 coarse

theorem actual_configuration_innovation_children_cross (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) (opened : Bool) :
    ∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive lessOne fixedPoint opened,
      ∀ address edge,
        rule.network.crosses
            (configurationInnovation rule (actualConfigurationSequence rule path) (address ++ [edge])) =
          configurationInnovation rule (actualConfigurationSequence rule path) address edge := by
  filter_upwards [Rule.ConfigurationHistory.infiniteLaw_coarsens rule p positive lessOne fixedPoint opened]
    with path coherent
  intro address edge
  exact configurationInnovation_child_crosses rule (actualConfigurationSequence rule path)
    coherent address edge

theorem actual_configuration_tree_coherent (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) (opened : Bool) :
    ∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive lessOne fixedPoint opened,
      ∀ address, configurationSequenceCoherent rule
        (configurationTree rule (actualConfigurationSequence rule path) address) := by
  filter_upwards [Rule.ConfigurationHistory.infiniteLaw_coarsens rule p positive lessOne fixedPoint opened]
    with path coherent
  intro address
  exact configurationTree_coherent rule (actualConfigurationSequence rule path) coherent address

theorem actual_configuration_tree_recursion (rule : Rule)
    (simple : Function.Injective (fun edge =>
      s((rule.network.endpoint edge).1, (rule.network.endpoint edge).2)))
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (opened : Bool) :
    ∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive lessOne fixedPoint opened,
      ∀ address depth,
        (((rule.generation (depth + 1)).network.openGraph
            (configurationTree rule (actualConfigurationSequence rule path) address (depth + 1))).dist
              (rule.generation (depth + 1)).network.source
              (rule.generation (depth + 1)).network.target : ℝ) =
          cellMinPlus rule.network (rule.generation depth).network
            (configurationInnovation rule (actualConfigurationSequence rule path) address)
            (fun edge => configurationTree rule (actualConfigurationSequence rule path)
              (address ++ [edge]) depth) := by
  filter_upwards [Rule.ConfigurationHistory.infiniteLaw_coarsens rule p positive lessOne fixedPoint opened]
    with path coherent
  intro address depth
  exact configurationTree_distance_recursion rule simple (actualConfigurationSequence rule path)
    coherent address depth

end IGSIII.Chemical.Substitution
