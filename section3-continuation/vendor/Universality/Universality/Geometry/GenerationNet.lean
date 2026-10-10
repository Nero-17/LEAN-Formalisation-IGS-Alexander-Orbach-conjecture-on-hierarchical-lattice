import Universality.Geometry.GenerationCompletion
import Mathlib.Analysis.SpecificLimits.Basic

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem substitute_vertex_near_old {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges)
    (inner : FiniteNetwork innerVertices innerEdges)
    (hinner : ∀ vertex, inner.fullGraph.Reachable inner.source vertex)
    (radius : ℕ) (hradius : ∀ vertex, inner.fullGraph.dist inner.source vertex ≤ radius)
    (vertex : Fin (Fintype.card (outer.SubstitutionVertex inner))) :
    ∃ old : Fin outerVertices, (outer.substitute inner).fullGraph.dist
      (Fintype.equivFin (outer.SubstitutionVertex inner) (Sum.inl old)) vertex ≤ radius := by
  obtain ⟨vertex, rfl⟩ := (Fintype.equivFin (outer.SubstitutionVertex inner)).surjective vertex
  cases vertex with
  | inl old => exact ⟨old, by simp⟩
  | inr pair =>
    rcases pair with ⟨edge, inside⟩
    obtain ⟨walk, hlength⟩ := (hinner inside.val).exists_walk_length_eq_dist
    have hsource : outer.cellVertex inner edge inner.source = Sum.inl (outer.endpoint edge).1 :=
      outer.cellVertex_source inner edge
    have htarget : outer.cellVertex inner edge inside.val = Sum.inr (edge, inside) := by
      simp [cellVertex, inside.property.1, inside.property.2]
    let lifted := ((walk.map (outer.cellHom inner (fun _ _ => true) edge)).copy hsource htarget).map
      (outer.substitutionGraphIso inner (fun _ _ => true)).toHom
    refine ⟨(outer.endpoint edge).1, (SimpleGraph.dist_le lifted).trans ?_⟩
    simpa only [lifted, SimpleGraph.Walk.length_map, SimpleGraph.Walk.length_copy, hlength]
      using hradius inside.val

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem Classical.generation_vertex_near_old {rule : Rule} (h : rule.Classical)
    (radius : ℕ) (hradius : ∀ vertex,
      rule.network.fullGraph.dist rule.network.source vertex ≤ radius)
    (depth : ℕ) (vertex : Fin (rule.generation (depth + 1)).vertices) :
    ∃ old : Fin (rule.generation depth).vertices,
      scaledGenerationDistance rule (depth + 1) (rule.generationOldVertex depth old) vertex ≤
        (radius : ℝ) /
          (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 2) := by
  obtain ⟨old, hbound⟩ := (rule.generation depth).network.substitute_vertex_near_old rule.network
    h.connected radius hradius vertex
  refine ⟨old, ?_⟩
  apply (div_le_div_iff_of_pos_right (pow_pos h.scale_real_pos _)).mpr
  exact_mod_cast hbound

end
end Universality.Rule

