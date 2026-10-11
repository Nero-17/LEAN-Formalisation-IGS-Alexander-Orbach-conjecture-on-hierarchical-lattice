import IGSIII34.ResistanceLimit.PairTriangle

/-!
# Rayleigh comparison under a genuine network embedding

Embedding the vertices and edges of a child network in a larger network can
only decrease its pair resistances. This includes the intrinsic distances of
each side of a noncrossing child and every one-terminal decoration.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000

namespace IGSIII34.ResistanceLimit
noncomputable section
open Resistance Resistance.FiniteNetwork
open scoped BigOperators

variable {Vertex Edge OtherVertex OtherEdge : Type*}
  [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
  [Fintype OtherVertex] [DecidableEq OtherVertex] [Fintype OtherEdge] [DecidableEq OtherEdge]

def networkEmbeddingGraphHom (child : Resistance.FiniteNetwork Vertex Edge)
    (parent : Resistance.FiniteNetwork OtherVertex OtherEdge)
    (vertices : Vertex ↪ OtherVertex) (edges : Edge ↪ OtherEdge)
    (endpoint : ∀ edge, parent.endpoint (edges edge) =
      (vertices (child.endpoint edge).1, vertices (child.endpoint edge).2)) :
    child.graph →g parent.graph where
  toFun := vertices
  map_rel' := by
    intro first last adjacent
    rcases adjacent with ⟨distinct, edge, orientation | orientation⟩
    · refine ⟨fun equality => distinct (vertices.injective equality), edges edge, Or.inl ?_⟩
      rw [endpoint, orientation]
    · refine ⟨fun equality => distinct (vertices.injective equality), edges edge, Or.inr ?_⟩
      rw [endpoint, orientation]

theorem embedded_potentialEnergy_le (child : Resistance.FiniteNetwork Vertex Edge)
    (parent : Resistance.FiniteNetwork OtherVertex OtherEdge)
    (vertices : Vertex ↪ OtherVertex) (edges : Edge ↪ OtherEdge)
    (endpoint : ∀ edge, parent.endpoint (edges edge) =
      (vertices (child.endpoint edge).1, vertices (child.endpoint edge).2))
    (childResistance : Edge → ℝ) (parentResistance : OtherEdge → ℝ)
    (parentPositive : ∀ edge, 0 < parentResistance edge)
    (resistanceMatch : ∀ edge, parentResistance (edges edge) = childResistance edge)
    (potential : OtherVertex → ℝ) :
    child.potentialEnergy childResistance (fun vertex => potential (vertices vertex)) ≤
      parent.potentialEnergy parentResistance potential := by
  unfold potentialEnergy
  calc
    _ = ∑ edge ∈ Finset.univ.image edges,
        (potential (parent.endpoint edge).1 - potential (parent.endpoint edge).2) ^ 2 / parentResistance edge := by
      rw [Finset.sum_image (fun first _ last _ equality => edges.injective equality)]
      apply Finset.sum_congr rfl
      intro edge _
      rw [endpoint, resistanceMatch]
    _ ≤ _ := Finset.sum_le_univ_sum_of_nonneg (fun edge => div_nonneg (sq_nonneg _) (parentPositive edge).le)

theorem embedded_pairResistance_le (child : Resistance.FiniteNetwork Vertex Edge)
    (parent : Resistance.FiniteNetwork OtherVertex OtherEdge)
    (vertices : Vertex ↪ OtherVertex) (edges : Edge ↪ OtherEdge)
    (endpoint : ∀ edge, parent.endpoint (edges edge) =
      (vertices (child.endpoint edge).1, vertices (child.endpoint edge).2))
    (childResistance : Edge → ℝ) (parentResistance : OtherEdge → ℝ)
    (childPositive : ∀ edge, 0 < childResistance edge) (parentPositive : ∀ edge, 0 < parentResistance edge)
    (resistanceMatch : ∀ edge, parentResistance (edges edge) = childResistance edge)
    (first last : Vertex) (reachable : child.graph.Reachable first last) :
    pairResistance parent parentResistance (vertices first) (vertices last) ≤
      pairResistance child childResistance first last := by
  by_cases distinct : first ≠ last
  · have liftedDistinct : vertices first ≠ vertices last := fun equality => distinct (vertices.injective equality)
    have parentReach : parent.graph.Reachable (vertices first) (vertices last) :=
      reachable.map (networkEmbeddingGraphHom child parent vertices edges endpoint)
    have childStrict := pairResistance_pos child childResistance childPositive distinct reachable
    have parentStrict := pairResistance_pos parent parentResistance parentPositive liftedDistinct parentReach
    obtain ⟨potential, atFirst, atLast, _, minimal⟩ := exists_pair_minimizer_in_unitInterval
      parent parentResistance parentPositive liftedDistinct parentReach
    have lower := pairResistance_energy_lower_bound child childResistance childPositive distinct reachable
      (fun vertex => potential (vertices vertex))
    rw [atFirst, atLast] at lower
    norm_num only [zero_sub, neg_one_sq, one_div] at lower
    have comparison := embedded_potentialEnergy_le child parent vertices edges endpoint
      childResistance parentResistance parentPositive resistanceMatch potential
    rw [minimal] at comparison
    exact (inv_le_inv₀ childStrict parentStrict).mp (lower.trans comparison)
  · have equal := not_ne_iff.mp distinct
    subst last
    rw [pairResistance_self, pairResistance_self]

end
end IGSIII34.ResistanceLimit
