import IGSIII34.ResistanceLimit.ActualBlockZeroPersistence
import IGSIII34.ResistanceLimit.SourceEnergy

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry

theorem sourceProjection_fixed_nonzero_reachable
    {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
    (network : Resistance.FiniteNetwork Vertex Edge) (potential : Vertex → ℝ)
    (projection : sourceProjection network potential = potential) (vertex : Vertex)
    (nonzero : potential vertex ≠ 0) : network.graph.Reachable network.source vertex := by
  classical
  by_contra absent
  have equal := congrFun projection vertex
  simp only [sourceProjection, if_neg absent] at equal
  exact nonzero equal.symm

/-- Every nonzero point of the actual finite zero extension is an original
vertex of the chosen cell; all other sockets and coarse junctions vanish. -/
theorem actualBlockZeroExtension_nonzero_birth
    (rule : Rule) (coarse fine : ℕ) (chosen : Fin (rule.generation coarse).edges)
    (supplied : Fin (rule.generation fine).vertices → ℝ)
    (vertex : Fin (rule.generation (coarse + fine + 1)).vertices)
    (nonzero : actualBlockZeroExtension rule coarse fine chosen supplied vertex ≠ 0) :
    ∃ localVertex : Fin (rule.generation fine).vertices,
      (generationBlockCellEmbedding rule coarse fine chosen).vertex localVertex = vertex ∧ supplied localVertex ≠ 0 := by
  classical
  let coordinates := ((Fintype.equivFin ((rule.generation coarse).network.SubstitutionVertex
    (rule.generation fine).network)).trans (rule.generationBlockDecomposition coarse fine).vertex.symm)
  obtain ⟨point, equality⟩ := coordinates.surjective vertex
  subst vertex
  cases point with
  | inl old =>
      have zero := actualBlockZeroExtension_old rule coarse fine chosen supplied old
      exact False.elim (nonzero zero)
  | inr pair =>
      rcases pair with ⟨other, inside⟩
      have interiorIdentity : (rule.generation coarse).network.cellVertex (rule.generation fine).network other inside.val =
          Sum.inr (other, inside) := by
        simp only [Universality.FiniteNetwork.cellVertex, dif_neg inside.property.1, dif_neg inside.property.2]
        rfl
      have birthIdentity : coordinates (Sum.inr (other, inside)) =
          (generationBlockCellEmbedding rule coarse fine other).vertex inside.val := by
        change _ = (rule.generationBlockDecomposition coarse fine).vertex.symm
          (Fintype.equivFin _ ((rule.generation coarse).network.cellVertex (rule.generation fine).network other inside.val))
        rw [interiorIdentity]
        rfl
      by_cases same : other = chosen
      · subst other
        refine ⟨inside.val, birthIdentity.symm, ?_⟩
        change supplied inside.val ≠ 0
        simpa only [actualBlockZeroExtension, coordinates, Equiv.trans_apply,
          Equiv.apply_symm_apply, Equiv.symm_apply_apply, cellZeroExtension, Sum.elim_inr,
          if_pos rfl, if_true] using nonzero
      · rw [birthIdentity] at nonzero
        exact False.elim (nonzero (actualBlockZeroExtension_other rule coarse fine chosen other same supplied inside.val))

end
end IGSIII34.ResistanceLimit
