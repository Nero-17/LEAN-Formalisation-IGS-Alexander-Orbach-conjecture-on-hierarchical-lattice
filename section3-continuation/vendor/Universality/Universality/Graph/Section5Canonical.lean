import Universality.Graph.Section5Structural

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {outerVertices outerEdges : ℕ}
variable {innerVertices innerEdges : Fin outerEdges → ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : (edge : Fin outerEdges) → FiniteNetwork (innerVertices edge) (innerEdges edge))

theorem heterogeneousConfiguration_update
    (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge))
    (edge : Fin outerEdges) (child : Fin (innerEdges edge)) (value : Bool) :
    Function.update (heterogeneousConfigurationEquiv configuration)
      (Fintype.equivFin _ ⟨edge, child⟩) value =
      heterogeneousConfigurationEquiv (Function.update configuration edge
        (Function.update (configuration edge) child value)) := by
  funext bond
  obtain ⟨⟨other, inside⟩, rfl⟩ := (Fintype.equivFin (Σ edge, Fin (innerEdges edge))).surjective bond
  by_cases same_edge : other = edge
  · subst other
    by_cases same_child : inside = child
    · subst inside
      simp only [Function.update_self, heterogeneousConfigurationEquiv_apply]
    · have different : Fintype.equivFin _ (⟨edge, inside⟩ : Σ edge, Fin (innerEdges edge)) ≠
          Fintype.equivFin _ ⟨edge, child⟩ := by
        intro equality
        exact same_child (eq_of_heq (Sigma.mk.inj_iff.mp ((Fintype.equivFin _).injective equality)).2)
      simp only [Function.update_of_ne different, heterogeneousConfigurationEquiv_apply,
        Function.update_self, Function.update_of_ne same_child]
  · have different : Fintype.equivFin _ (⟨other, inside⟩ : Σ edge, Fin (innerEdges edge)) ≠
        Fintype.equivFin _ ⟨edge, child⟩ := by
      intro equality
      exact same_edge (congrArg Sigma.fst ((Fintype.equivFin _).injective equality))
    simp only [Function.update_of_ne different, heterogeneousConfigurationEquiv_apply,
      Function.update_of_ne same_edge]

theorem exists_pivotal_heterogeneousSubstitute
    (inner_connected : ∀ edge, (S edge).fullGraph.Reachable (S edge).source (S edge).target)
    (edge : Fin outerEdges) (child : Fin (innerEdges edge))
    (outerConfiguration : Configuration outerEdges) (innerConfiguration : Configuration (innerEdges edge))
    (outer_pivotal : R.pivotal outerConfiguration edge = true)
    (inner_pivotal : (S edge).pivotal innerConfiguration child = true) :
    ∃ configuration, (R.heterogeneousSubstitute S).pivotal configuration
      (Fintype.equivFin _ ⟨edge, child⟩) = true := by
  classical
  let cells : (other : Fin outerEdges) → Configuration (innerEdges other) :=
    Function.update (fun other _ => outerConfiguration other) edge innerConfiguration
  have coarse (value : Bool) :
      heterogeneousCoarseConfiguration S
        (Function.update cells edge (Function.update (cells edge) child value)) =
        Function.update outerConfiguration edge ((S edge).crosses
          (Function.update innerConfiguration child value)) := by
    funext other
    by_cases same_edge : other = edge
    · subst other
      simp [heterogeneousCoarseConfiguration, cells]
    · simp only [heterogeneousCoarseConfiguration, Function.update_of_ne same_edge]
      simp only [cells, Function.update_of_ne same_edge]
      cases state : outerConfiguration other
      · exact (S other).crosses_all_closed
      · exact ((S other).crosses_eq_true _).mpr (inner_connected other)
  refine ⟨heterogeneousConfigurationEquiv cells, ?_⟩
  have conditions :
      (S edge).crosses (Function.update innerConfiguration child true) = true ∧
      (S edge).crosses (Function.update innerConfiguration child false) = false := by
    simpa [pivotal] using inner_pivotal
  obtain ⟨opened, closed⟩ := conditions
  simp only [pivotal, heterogeneousConfiguration_update, R.heterogeneousSubstitute_crosses S,
    coarse, opened, closed]
  exact outer_pivotal

theorem heterogeneousSubstitute_canonical
    (outer_simple : Function.Injective (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2)))
    (inner_simple : ∀ edge, Function.Injective
      (fun child => s(((S edge).endpoint child).1, ((S edge).endpoint child).2)))
    (inner_connected : ∀ edge, (S edge).fullGraph.Reachable (S edge).source (S edge).target)
    (outer_canonical : ∀ edge, ∃ walk : R.fullGraph.Walk R.source R.target,
      walk.IsPath ∧ s((R.endpoint edge).1, (R.endpoint edge).2) ∈ walk.edges)
    (inner_canonical : ∀ edge child,
      ∃ walk : (S edge).fullGraph.Walk (S edge).source (S edge).target,
      walk.IsPath ∧ s(((S edge).endpoint child).1, ((S edge).endpoint child).2) ∈ walk.edges) :
    ∀ edge, ∃ walk : (R.heterogeneousSubstitute S).fullGraph.Walk
      (R.heterogeneousSubstitute S).source (R.heterogeneousSubstitute S).target,
      walk.IsPath ∧ s(((R.heterogeneousSubstitute S).endpoint edge).1,
        ((R.heterogeneousSubstitute S).endpoint edge).2) ∈ walk.edges := by
  intro bond
  obtain ⟨⟨edge, child⟩, rfl⟩ := (Fintype.equivFin (Σ edge, Fin (innerEdges edge))).surjective bond
  obtain ⟨outerPath, outer_isPath, outer_mem⟩ := outer_canonical edge
  obtain ⟨innerPath, inner_isPath, inner_mem⟩ := inner_canonical edge child
  obtain ⟨outerConfiguration, outer_pivotal⟩ :=
    R.exists_pivotal_of_path outer_simple edge outerPath outer_isPath outer_mem
  obtain ⟨innerConfiguration, inner_pivotal⟩ :=
    (S edge).exists_pivotal_of_path (inner_simple edge) child innerPath inner_isPath inner_mem
  obtain ⟨configuration, configuration_pivotal⟩ := R.exists_pivotal_heterogeneousSubstitute S
    inner_connected edge child outerConfiguration innerConfiguration outer_pivotal inner_pivotal
  exact (R.heterogeneousSubstitute S).path_of_pivotal _ configuration configuration_pivotal

end
end Universality.FiniteNetwork
