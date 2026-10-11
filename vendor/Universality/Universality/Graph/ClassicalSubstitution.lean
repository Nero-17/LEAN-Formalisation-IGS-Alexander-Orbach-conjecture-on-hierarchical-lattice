import Universality.Graph.ClassicalRule
import Universality.Graph.SubstitutionFullConnectivity
import Universality.Graph.SubstitutionSimple
import Universality.Graph.SubstitutionInvolution
import Universality.Graph.SubstitutionPivotal

namespace Universality.Rule
noncomputable section

/-- Every finite classical rule condition is preserved by edge substitution,
including simplicity, canonicality and an involutive terminal exchange. -/
theorem Classical.mul {outer inner : Rule} (houter : outer.Classical) (hinner : inner.Classical) :
    (outer * inner).Classical where
  connected := outer.network.substitute_all_vertices_connected inner.network houter.connected hinner.connected
  simple := outer.network.substitute_simple inner.network hinner.simple hinner.scale
  canonical := outer.network.substitute_canonical inner.network houter.simple hinner.simple
    (hinner.connected _) houter.canonical hinner.canonical
  scale := (houter.massAdmissible.mul hinner.massAdmissible).scale
  cut := (houter.massAdmissible.mul hinner.massAdmissible).cut
  symmetric := by
    obtain ⟨outerSymmetry, houterInvolution, houterSource⟩ := houter.symmetric
    obtain ⟨innerSymmetry, hinnerInvolution, hinnerSource⟩ := hinner.symmetric
    have hinnerTarget : innerSymmetry.vertex inner.network.target = inner.network.source := by
      rw [← hinnerSource]
      exact hinnerInvolution _
    refine ⟨outerSymmetry.substitute innerSymmetry hinnerSource hinnerTarget, ?_, ?_⟩
    · exact outerSymmetry.substitute_vertex_involutive innerSymmetry hinnerSource hinnerTarget
        houterInvolution hinnerInvolution (outerSymmetry.edge_involutive houter.simple houterInvolution)
    · exact outerSymmetry.substitute_source innerSymmetry hinnerSource hinnerTarget houterSource

theorem Classical.generation {rule : Rule} (h : rule.Classical) (n : ℕ) :
    (rule.generation n).Classical := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.mul h

end
end Universality.Rule
