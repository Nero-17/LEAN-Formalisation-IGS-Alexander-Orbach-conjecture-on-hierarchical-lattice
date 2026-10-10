import Universality.Graph.SubstitutionDistance
import Universality.Graph.SubstitutionFullConnectivity

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- A source-radius bound for the actual substituted graph. The coarse part
uses terminal geodesics, rather than the diameter of the inner graph. -/
theorem substitute_source_distance_bound
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (outerBound innerBound : ℕ)
    (houterBound : ∀ vertex, R.fullGraph.dist R.source vertex ≤ outerBound)
    (hinnerBound : ∀ vertex, S.fullGraph.dist S.source vertex ≤ innerBound)
    (vertex : Fin (Fintype.card (R.SubstitutionVertex S))) :
    (R.substitute S).fullGraph.dist (R.substitute S).source vertex ≤
      outerBound * S.fullGraph.dist S.source S.target + innerBound := by
  let certificate := DistanceCertificate.ofReachable S (hinner S.target)
  have hcoarse (old : Fin outerVertices) :
      ∃ walk : (R.substitutedGraph S (fun _ _ => true)).Walk
          (Sum.inl R.source) (Sum.inl old),
        walk.length ≤ outerBound * S.fullGraph.dist S.source S.target := by
    obtain ⟨shortest, hlength⟩ := (houter old).exists_walk_length_eq_dist
    obtain ⟨lifted, hlifted⟩ := R.substituted_walk_length S certificate shortest
    refine ⟨lifted, ?_⟩
    rw [hlifted, hlength]
    exact Nat.mul_le_mul_right _ (houterBound old)
  obtain ⟨vertex, rfl⟩ := (Fintype.equivFin (R.SubstitutionVertex S)).surjective vertex
  suffices ∃ walk : (R.substitutedGraph S (fun _ _ => true)).Walk
      (Sum.inl R.source) vertex,
      walk.length ≤ outerBound * S.fullGraph.dist S.source S.target + innerBound by
    obtain ⟨walk, hwalk⟩ := this
    exact (SimpleGraph.dist_le (walk.map
      (R.substitutionGraphIso S (fun _ _ => true)).toHom)).trans
        (by simpa only [SimpleGraph.Walk.length_map] using hwalk)
  cases vertex with
  | inl old =>
      obtain ⟨walk, hwalk⟩ := hcoarse old
      exact ⟨walk, hwalk.trans (Nat.le_add_right _ _)⟩
  | inr pair =>
      rcases pair with ⟨edge, inside⟩
      obtain ⟨coarse, hcoarse⟩ := hcoarse (R.endpoint edge).1
      obtain ⟨localWalk, hlocal⟩ := (hinner inside.val).exists_walk_length_eq_dist
      let mapped := localWalk.map (R.cellHom S (fun _ _ => true) edge)
      have hstart : R.cellVertex S edge S.source = Sum.inl (R.endpoint edge).1 :=
        R.cellVertex_source S edge
      have hend : R.cellVertex S edge inside.val = Sum.inr (edge, inside) := by
        simp [cellVertex, inside.property.1, inside.property.2]
      refine ⟨coarse.append (mapped.copy hstart hend), ?_⟩
      dsimp only [mapped]
      rw [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_copy,
        SimpleGraph.Walk.length_map, hlocal]
      exact Nat.add_le_add hcoarse (hinnerBound inside.val)

end
end Universality.FiniteNetwork
