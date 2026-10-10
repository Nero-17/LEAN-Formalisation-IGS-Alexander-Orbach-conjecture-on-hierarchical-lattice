import Universality.Graph.SubstitutionDistance

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- Every pair of old vertices has its exact distance multiplied by the
inner terminal distance. This is not restricted to the two outer terminals. -/
theorem substitute_coarse_distance (u v : Fin outerVertices)
    (houter : R.fullGraph.Reachable u v)
    (hinner : S.fullGraph.Reachable S.source S.target) :
    (R.substitute S).fullGraph.dist
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl u))
      (Fintype.equivFin (R.SubstitutionVertex S) (Sum.inl v)) =
      R.fullGraph.dist u v * S.fullGraph.dist S.source S.target := by
  by_cases heq : u = v
  · subst v
    simp
  · let rerooted : FiniteNetwork outerVertices outerEdges :=
      { R with source := u, target := v, terminals_distinct := heq }
    exact rerooted.substitute_terminal_distance S houter hinner

end
end Universality.FiniteNetwork
