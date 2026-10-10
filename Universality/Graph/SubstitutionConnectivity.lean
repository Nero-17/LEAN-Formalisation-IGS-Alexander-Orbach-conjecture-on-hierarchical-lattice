import Universality.Percolation.FiniteMassDimension

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem substitute_crosses (ω : Fin outerEdges → Configuration innerEdges) :
    (R.substitute S).crosses (substitutionConfigurationEquiv ω) =
      R.crosses (S.coarseConfiguration ω) := by
  change (R.substitute S).conditioning .connected (substitutionConfigurationEquiv ω) =
    R.conditioning .connected (S.coarseConfiguration ω)
  rw [substitute_conditioning, substitutedConditioning_eq]

theorem substitute_full_connected
    (houter : R.fullGraph.Reachable R.source R.target)
    (hinner : S.fullGraph.Reachable S.source S.target) :
    (R.substitute S).fullGraph.Reachable (R.substitute S).source (R.substitute S).target := by
  apply ((R.substitute S).crosses_eq_true (fun _ => true)).mp
  change (R.substitute S).crosses
    (substitutionConfigurationEquiv (fun (_ : Fin outerEdges) (_ : Fin innerEdges) => true)) = true
  rw [substitute_crosses]
  have hcoarse : S.coarseConfiguration (fun (_ : Fin outerEdges) (_ : Fin innerEdges) => true) =
      (fun _ => true) := by
    funext edge
    exact (S.crosses_eq_true _).mpr hinner
  rw [hcoarse]
  exact (R.crosses_eq_true _).mpr houter

theorem substitution_onlyClosed_cells (edge : Fin outerEdges) (child : Fin innerEdges) :
    (substitutionConfigurationEquiv (outerEdges := outerEdges) (innerEdges := innerEdges)).symm
      (onlyClosed (finProdFinEquiv (edge, child))) =
        fun other => if other = edge then onlyClosed child else fun _ => true := by
  funext other bond
  change Function.update (fun _ => true) (finProdFinEquiv (edge, child)) false
    (finProdFinEquiv (other, bond)) = _
  by_cases ho : other = edge
  · subst other
    by_cases hb : bond = child
    · subst bond
      simp [onlyClosed]
    · have hne : finProdFinEquiv (edge, bond) ≠ finProdFinEquiv (edge, child) := by
        intro h
        exact hb (congrArg Prod.snd (finProdFinEquiv.injective h))
      simp [onlyClosed, hb, hne]
  · have hne : finProdFinEquiv (other, bond) ≠ finProdFinEquiv (edge, child) := by
      intro h
      exact ho (congrArg Prod.fst (finProdFinEquiv.injective h))
    simp [ho, hne]

theorem substitute_survives_single_deletion
    (houter : R.fullGraph.Reachable R.source R.target)
    (hinner : S.fullGraph.Reachable S.source S.target)
    (hcut : ∀ child, S.crosses (onlyClosed child) = true) :
    ∀ edge, (R.substitute S).crosses (onlyClosed edge) = true := by
  intro edge
  obtain ⟨pair, rfl⟩ := finProdFinEquiv.surjective edge
  rcases pair with ⟨edge, child⟩
  have hconfig := (substitutionConfigurationEquiv (outerEdges := outerEdges)
    (innerEdges := innerEdges)).apply_symm_apply (onlyClosed (finProdFinEquiv (edge, child)))
  rw [← hconfig, substitute_crosses, substitution_onlyClosed_cells]
  have hcoarse : S.coarseConfiguration (fun other : Fin outerEdges =>
      if other = edge then onlyClosed child else fun _ => true) = (fun _ => true) := by
    funext other
    unfold coarseConfiguration
    by_cases he : other = edge
    · simp only [he, ↓reduceIte]
      exact hcut child
    · simp only [he, ↓reduceIte]
      exact (S.crosses_eq_true _).mpr hinner
  rw [hcoarse]
  exact (R.crosses_eq_true _).mpr houter

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- Sufficient finite-rule conditions for the mass-growth and spectral results.
This deliberately does not claim to encode all the manuscript's requirements
of simplicity and canonicality. -/
structure MassAdmissible (rule : Rule) : Prop where
  connected : rule.network.fullGraph.Reachable rule.network.source rule.network.target
  scale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target
  cut : ∀ edge, rule.network.crosses (onlyClosed edge) = true
  symmetric : rule.TerminalSymmetric

theorem MassAdmissible.mul {outer inner : Rule}
    (houter : outer.MassAdmissible) (hinner : inner.MassAdmissible) :
    (outer * inner).MassAdmissible where
  connected := outer.network.substitute_full_connected inner.network houter.connected hinner.connected
  scale := by
    change 1 < (outer.network.substitute inner.network).fullGraph.dist
      (outer.network.substitute inner.network).source (outer.network.substitute inner.network).target
    rw [substitute_terminal_distance _ _ houter.connected hinner.connected]
    nlinarith [houter.scale, hinner.scale]
  cut := outer.network.substitute_survives_single_deletion inner.network
    houter.connected hinner.connected hinner.cut
  symmetric := houter.symmetric.mul hinner.symmetric

end
end Universality.Rule
