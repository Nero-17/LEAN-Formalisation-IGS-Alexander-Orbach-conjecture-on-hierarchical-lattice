import IGSIII.Chemical.SubstitutionPaths.History

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
# Compatibility of actual child configurations across the history

Reassociation acts on indexed edges by the explicit product associator.
Consequently extracting a top child commutes with coarsening one generation.
This identifies the extracted root with the original history's first
configuration and gives coherent actual histories in every child.
-/

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

theorem generationTopCells_apply (rule : Rule) (depth : ℕ)
    (fine : Configuration (rule.generation (depth + 1)).edges)
    (edge : Fin rule.edges) (child : Fin (rule.generation depth).edges) :
    generationTopCells rule depth fine edge child =
      fine ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child))) := rfl

theorem generationTopCells_succ_apply (rule : Rule) (depth : ℕ)
    (fine : Configuration (rule.generation (depth + 2)).edges)
    (edge : Fin rule.edges) (child : Fin (rule.generation depth).edges) (leaf : Fin rule.edges) :
    generationTopCells rule (depth + 1) fine edge (finProdFinEquiv (child, leaf)) =
      fine (finProdFinEquiv
        ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child)), leaf)) := by
  rw [generationTopCells_apply]
  apply congrArg fine
  apply (rule.generationTopDecomposition (depth + 1)).edge.injective
  rw [Equiv.apply_symm_apply]
  change finProdFinEquiv (edge, finProdFinEquiv (child, leaf)) =
    substitutionAssociatorEdge
      (finProdFinEquiv (Prod.map (rule.generationTopDecomposition depth).edge id
        (finProdFinEquiv.symm (finProdFinEquiv
          ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child)), leaf)))))
  rw [Equiv.symm_apply_apply]
  change _ = substitutionAssociatorEdge (finProdFinEquiv
    ((rule.generationTopDecomposition depth).edge
      ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child))), leaf))
  rw [Equiv.apply_symm_apply, substitutionAssociatorEdge_apply]

theorem generationTopCells_coarsen (rule : Rule) (depth : ℕ)
    (fine : Configuration (rule.generation (depth + 2)).edges) (edge : Fin rule.edges) :
    generationTopCells rule depth (rule.coarsenGeneration (depth + 1) fine) edge =
      rule.coarsenGeneration depth (generationTopCells rule (depth + 1) fine edge) := by
  funext child
  rw [generationTopCells_apply]
  change rule.network.crosses (fun leaf => fine (finProdFinEquiv
      ((rule.generationTopDecomposition depth).edge.symm (finProdFinEquiv (edge, child)), leaf))) =
    rule.network.crosses (fun leaf =>
      generationTopCells rule (depth + 1) fine edge (finProdFinEquiv (child, leaf)))
  congr 1
  funext leaf
  exact (generationTopCells_succ_apply rule depth fine edge child leaf).symm

theorem generation_crosses_coarsen (rule : Rule) (depth : ℕ)
    (fine : Configuration (rule.generation (depth + 1)).edges) :
    (rule.generation (depth + 1)).network.crosses fine =
      (rule.generation depth).network.crosses (rule.coarsenGeneration depth fine) := by
  have identity := FiniteNetwork.substitute_crosses (rule.generation depth).network rule.network
    (substitutionConfigurationEquiv.symm fine)
  simp only [Equiv.apply_symm_apply] at identity
  exact identity

theorem generationRootConfiguration_zero (rule : Rule)
    (fine : Configuration (rule.generation 1).edges) :
    generationRootConfiguration rule 0 fine = rule.coarsenGeneration 0 fine := rfl

theorem generationRootConfiguration_coarsen (rule : Rule) (depth : ℕ)
    (fine : Configuration (rule.generation (depth + 2)).edges) :
    generationRootConfiguration rule (depth + 1) fine =
      generationRootConfiguration rule depth (rule.coarsenGeneration (depth + 1) fine) := by
  funext edge
  change (rule.generation (depth + 1)).network.crosses
      (generationTopCells rule (depth + 1) fine edge) =
    (rule.generation depth).network.crosses
      (generationTopCells rule depth (rule.coarsenGeneration (depth + 1) fine) edge)
  rw [generation_crosses_coarsen, generationTopCells_coarsen]

noncomputable def initialConfiguration (rule : Rule) :
    (depth : ℕ) → rule.ConfigurationHistory depth → Configuration rule.edges
  | 0, history => history
  | depth + 1, history => initialConfiguration rule depth history.1

/-- The extracted root is exactly the history's original configuration. -/
theorem historyRootConfiguration_eq_initial (rule : Rule) (depth : ℕ)
    (history : rule.ConfigurationHistory (depth + 1))
    (coherent : Rule.ConfigurationHistory.coherent rule (depth + 1) history) :
    historyRootConfiguration rule depth history = initialConfiguration rule (depth + 1) history := by
  induction depth with
  | zero => exact coherent.2
  | succ depth inductionHypothesis =>
      change generationRootConfiguration rule (depth + 1) history.2 =
        initialConfiguration rule (depth + 1) history.1
      rw [generationRootConfiguration_coarsen, coherent.2]
      exact inductionHypothesis history.1 coherent.1

/-- Every child carries the actual history obtained by coarsening its finest
configuration. This definition retains noncrossing configurations as well. -/
noncomputable def historyChildHistory (rule : Rule) (depth : ℕ)
    (history : rule.ConfigurationHistory (depth + 1)) (edge : Fin rule.edges) :
    rule.ConfigurationHistory depth :=
  Rule.ConfigurationHistory.ofFine rule depth (historyChildConfiguration rule depth history edge)

theorem historyChildHistory_latest (rule : Rule) (depth : ℕ)
    (history : rule.ConfigurationHistory (depth + 1)) (edge : Fin rule.edges) :
    Rule.ConfigurationHistory.latest rule depth (historyChildHistory rule depth history edge) =
      historyChildConfiguration rule depth history edge :=
  Rule.ConfigurationHistory.latest_ofFine rule depth _

theorem historyChildHistory_coherent (rule : Rule) (depth : ℕ)
    (history : rule.ConfigurationHistory (depth + 1)) (edge : Fin rule.edges) :
    Rule.ConfigurationHistory.coherent rule depth (historyChildHistory rule depth history edge) := by
  apply (Rule.ConfigurationHistory.coherent_iff_ofFine rule depth _).mpr
  rw [historyChildHistory_latest]
  rfl

/-- On coherent histories, the extracted child histories extend rather than
being unrelated samples drawn separately at different depths. -/
theorem historyChildHistory_extends (rule : Rule) (depth : ℕ)
    (history : rule.ConfigurationHistory (depth + 2))
    (coherent : Rule.ConfigurationHistory.coherent rule (depth + 2) history)
    (edge : Fin rule.edges) :
    (historyChildHistory rule (depth + 1) history edge).1 =
      historyChildHistory rule depth history.1 edge := by
  change Rule.ConfigurationHistory.ofFine rule depth
      (rule.coarsenGeneration depth (generationTopCells rule (depth + 1) history.2 edge)) =
    Rule.ConfigurationHistory.ofFine rule depth
      (generationTopCells rule depth (Rule.ConfigurationHistory.latest rule (depth + 1) history.1) edge)
  rw [← generationTopCells_coarsen, coherent.2]

theorem infinite_history_root_eq_initial (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) (opened : Bool) :
    ∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive lessOne fixedPoint opened,
      ∀ depth, historyRootConfiguration rule depth (path (depth + 1)) = path 0 := by
  filter_upwards [Rule.ConfigurationHistory.infiniteLaw_coherent rule p positive lessOne fixedPoint opened,
    Rule.ConfigurationHistory.infiniteLaw_extends rule p positive lessOne fixedPoint opened]
      with path coherent compatible
  have initial : ∀ depth, initialConfiguration rule depth (path depth) = path 0 := by
    intro depth
    induction depth with
    | zero => rfl
    | succ depth inductionHypothesis =>
        change initialConfiguration rule depth (path (depth + 1)).1 = path 0
        rw [compatible depth]
        exact inductionHypothesis
  intro depth
  rw [historyRootConfiguration_eq_initial rule depth _ (coherent (depth + 1))]
  exact initial (depth + 1)

theorem infinite_history_children_extend (rule : Rule) (p : ℝ) (positive : 0 < p)
    (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p) (opened : Bool) :
    ∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive lessOne fixedPoint opened,
      ∀ depth edge, (historyChildHistory rule (depth + 1) (path (depth + 2)) edge).1 =
        historyChildHistory rule depth (path (depth + 1)) edge := by
  filter_upwards [Rule.ConfigurationHistory.infiniteLaw_coherent rule p positive lessOne fixedPoint opened,
    Rule.ConfigurationHistory.infiniteLaw_extends rule p positive lessOne fixedPoint opened]
      with path coherent compatible
  intro depth edge
  rw [historyChildHistory_extends rule depth _ (coherent (depth + 2)), compatible (depth + 1)]

end IGSIII.Chemical.Substitution
