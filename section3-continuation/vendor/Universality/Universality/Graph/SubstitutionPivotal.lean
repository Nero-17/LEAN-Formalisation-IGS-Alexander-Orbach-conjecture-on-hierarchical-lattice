import Universality.Graph.CanonicalPivotal
import Universality.Graph.SubstitutionConnectivity

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem substitutionConfiguration_update (configuration : Fin outerEdges → Configuration innerEdges)
    (edge : Fin outerEdges) (child : Fin innerEdges) (value : Bool) :
    Function.update (substitutionConfigurationEquiv configuration) (finProdFinEquiv (edge, child)) value =
      substitutionConfigurationEquiv (Function.update configuration edge
        (Function.update (configuration edge) child value)) := by
  have happ (cells : Fin outerEdges → Configuration innerEdges) (other : Fin outerEdges) (inside : Fin innerEdges) :
      substitutionConfigurationEquiv cells (finProdFinEquiv (other, inside)) = cells other inside := by
    change cells (finProdFinEquiv.symm (finProdFinEquiv (other, inside))).1
      (finProdFinEquiv.symm (finProdFinEquiv (other, inside))).2 = _
    rw [Equiv.symm_apply_apply]
  funext bond
  obtain ⟨⟨other, inside⟩, rfl⟩ := finProdFinEquiv.surjective bond
  by_cases he : other = edge
  · subst other
    by_cases hi : inside = child
    · subst inside; simp only [Function.update_self, happ]
    · have hne : finProdFinEquiv (edge, inside) ≠ finProdFinEquiv (edge, child) := by
        intro h; exact hi (congrArg Prod.snd (finProdFinEquiv.injective h))
      simp only [Function.update_of_ne hne, happ, Function.update_self, Function.update_of_ne hi]
  · have hne : finProdFinEquiv (other, inside) ≠ finProdFinEquiv (edge, child) := by
      intro h; exact he (congrArg Prod.fst (finProdFinEquiv.injective h))
    simp only [Function.update_of_ne hne, happ, Function.update_of_ne he]

theorem exists_pivotal_substitute
    (hconnected : S.fullGraph.Reachable S.source S.target)
    (edge : Fin outerEdges) (child : Fin innerEdges)
    (outerConfiguration : Configuration outerEdges) (innerConfiguration : Configuration innerEdges)
    (houter : R.pivotal outerConfiguration edge = true)
    (hinner : S.pivotal innerConfiguration child = true) :
    ∃ configuration, (R.substitute S).pivotal configuration (finProdFinEquiv (edge, child)) = true := by
  classical
  let cells : Fin outerEdges → Configuration innerEdges := fun other =>
    if other = edge then innerConfiguration else fun _ => outerConfiguration other
  have hcoarse (value : Bool) :
      S.coarseConfiguration (Function.update cells edge (Function.update (cells edge) child value)) =
        Function.update outerConfiguration edge (S.crosses (Function.update innerConfiguration child value)) := by
    funext other
    by_cases he : other = edge
    · subst other
      simp [coarseConfiguration, cells]
    · simp only [coarseConfiguration, Function.update_of_ne he]
      simp only [cells, if_neg he]
      cases hstate : outerConfiguration other
      · exact S.crosses_all_closed
      · exact (S.crosses_eq_true _).mpr hconnected
  refine ⟨substitutionConfigurationEquiv cells, ?_⟩
  have hconditions : S.crosses (Function.update innerConfiguration child true) = true ∧
      S.crosses (Function.update innerConfiguration child false) = false := by
    simpa [pivotal] using hinner
  obtain ⟨hopen, hclosed⟩ := hconditions
  simp only [pivotal, substitutionConfiguration_update, R.substitute_crosses S, hcoarse, hopen, hclosed]
  exact houter

theorem substitute_canonical
    (hsimple : Function.Injective (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2)))
    (hsimple' : Function.Injective (fun edge => s((S.endpoint edge).1, (S.endpoint edge).2)))
    (hconnected : S.fullGraph.Reachable S.source S.target)
    (houter : ∀ edge, ∃ walk : R.fullGraph.Walk R.source R.target,
      walk.IsPath ∧ s((R.endpoint edge).1, (R.endpoint edge).2) ∈ walk.edges)
    (hinner : ∀ edge, ∃ walk : S.fullGraph.Walk S.source S.target,
      walk.IsPath ∧ s((S.endpoint edge).1, (S.endpoint edge).2) ∈ walk.edges) :
    ∀ edge, ∃ walk : (R.substitute S).fullGraph.Walk (R.substitute S).source (R.substitute S).target,
      walk.IsPath ∧ s(((R.substitute S).endpoint edge).1, ((R.substitute S).endpoint edge).2) ∈ walk.edges := by
  intro bond
  obtain ⟨⟨edge, child⟩, rfl⟩ := finProdFinEquiv.surjective bond
  obtain ⟨outerPath, houterPath, houterMem⟩ := houter edge
  obtain ⟨innerPath, hinnerPath, hinnerMem⟩ := hinner child
  obtain ⟨outerConfiguration, hpivotal⟩ := R.exists_pivotal_of_path hsimple edge outerPath houterPath houterMem
  obtain ⟨innerConfiguration, hpivotal'⟩ := S.exists_pivotal_of_path hsimple' child innerPath hinnerPath hinnerMem
  obtain ⟨configuration, hconfiguration⟩ := R.exists_pivotal_substitute S hconnected edge child
    outerConfiguration innerConfiguration hpivotal hpivotal'
  exact (R.substitute S).path_of_pivotal _ configuration hconfiguration

end
end Universality.FiniteNetwork
