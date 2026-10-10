import Universality.Graph.CellIsometry
import Universality.Graph.NetworkEmbedding

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {vertices edges : ℕ} (network : FiniteNetwork vertices edges)

def boundaryDistance (vertex : Fin vertices) : ℝ :=
  min (network.fullGraph.dist network.source vertex : ℝ)
    (network.fullGraph.dist network.target vertex : ℝ)

theorem boundaryDistance_nonneg (vertex : Fin vertices) : 0 ≤ network.boundaryDistance vertex :=
  le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)

@[simp] theorem boundaryDistance_source : network.boundaryDistance network.source = 0 := by
  simp [boundaryDistance]

@[simp] theorem boundaryDistance_target : network.boundaryDistance network.target = 0 := by
  simp [boundaryDistance]

theorem boundaryDistance_adj {first second : Fin vertices} (hadj : network.fullGraph.Adj first second) :
    |network.boundaryDistance first - network.boundaryDistance second| ≤ 1 := by
  exact (abs_min_sub_min_le_max _ _ _ _).trans (max_le
    (graph_distance_height_adj network.fullGraph network.source hadj)
    (graph_distance_height_adj network.fullGraph network.target hadj))

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)

def boundaryPotential (weight : Fin outerEdges → ℝ) : outer.SubstitutionVertex inner → ℝ :=
  outer.substitutionPotential inner (fun _ => 0) (fun edge vertex => weight edge * inner.boundaryDistance vertex)

@[simp] theorem boundaryPotential_cell (weight : Fin outerEdges → ℝ)
    (edge : Fin outerEdges) (vertex : Fin innerVertices) :
    outer.boundaryPotential inner weight (outer.cellVertex inner edge vertex) =
      weight edge * inner.boundaryDistance vertex := by
  exact outer.substitutionPotential_cell inner (fun _ => 0)
    (fun edge vertex => weight edge * inner.boundaryDistance vertex)
    (fun edge => by simp) (fun edge => by simp) edge vertex

@[simp] theorem boundaryPotential_old (weight : Fin outerEdges → ℝ) (vertex : Fin outerVertices) :
    outer.boundaryPotential inner weight (Sum.inl vertex) = 0 := rfl

theorem boundaryPotential_adj (weight : Fin outerEdges → ℝ) (hweight : ∀ edge, |weight edge| ≤ 1)
    {first second : outer.SubstitutionVertex inner}
    (hadj : (outer.substitutedGraph inner (fun _ _ => true)).Adj first second) :
    |outer.boundaryPotential inner weight first - outer.boundaryPotential inner weight second| ≤ 1 := by
  apply outer.substitutionPotential_adj inner (fun _ => 0)
    (fun edge vertex => weight edge * inner.boundaryDistance vertex)
    (fun edge => by simp) (fun edge => by simp) ?_ hadj
  intro edge u v huv
  rw [← mul_sub, abs_mul]
  exact (mul_le_mul (hweight edge) (inner.boundaryDistance_adj huv) (abs_nonneg _) zero_le_one).trans
    (by norm_num)

theorem boundaryPotential_distance
    (houter : ∀ vertex, outer.fullGraph.Reachable outer.source vertex)
    (hinner : ∀ vertex, inner.fullGraph.Reachable inner.source vertex)
    (weight : Fin outerEdges → ℝ) (hweight : ∀ edge, |weight edge| ≤ 1)
    (first second : outer.SubstitutionVertex inner) :
    |outer.boundaryPotential inner weight first - outer.boundaryPotential inner weight second| ≤
      ((outer.substitute inner).fullGraph.dist
        (Fintype.equivFin (outer.SubstitutionVertex inner) first)
        (Fintype.equivFin (outer.SubstitutionVertex inner) second) : ℝ) := by
  have hfull := ((outer.substitute_all_vertices_connected inner houter hinner (Fintype.equivFin _ first)).symm).trans
    (outer.substitute_all_vertices_connected inner houter hinner
      (Fintype.equivFin (outer.SubstitutionVertex inner) second))
  have hraw := hfull.map (outer.substitutionGraphIso inner (fun _ _ => true)).symm.toHom
  change (outer.substitutedGraph inner (fun _ _ => true)).Reachable
    ((Fintype.equivFin _).symm (Fintype.equivFin _ first))
    ((Fintype.equivFin _).symm (Fintype.equivFin _ second)) at hraw
  simp only [Equiv.symm_apply_apply] at hraw
  have hbound := graph_height_distance_bound _ (outer.boundaryPotential inner weight)
    (outer.boundaryPotential_adj inner weight hweight) hraw
  have hisometry := graph_iso_distance_of_reachable
    (outer.substitutionGraphIso inner (fun _ _ => true)) hraw
  exact hbound.trans_eq (by exact_mod_cast hisometry.symm)

/-- Escaping a cell to any old vertex costs at least the local distance to
its boundary. This estimate does not use an upper bound on vertex degrees. -/
theorem substitute_cell_boundary_le_distance_to_old
    (houter : ∀ vertex, outer.fullGraph.Reachable outer.source vertex)
    (hinner : ∀ vertex, inner.fullGraph.Reachable inner.source vertex)
    (edge : Fin outerEdges) (vertex : Fin innerVertices) (old : Fin outerVertices) :
    inner.boundaryDistance vertex ≤
      ((outer.substitute inner).fullGraph.dist
        (Fintype.equivFin _ (outer.cellVertex inner edge vertex))
        (Fintype.equivFin _ (Sum.inl old)) : ℝ) := by
  have hbound := outer.boundaryPotential_distance inner houter hinner (fun _ => 1)
    (fun _ => by norm_num) (outer.cellVertex inner edge vertex) (Sum.inl old)
  simpa only [boundaryPotential_cell, boundaryPotential_old, one_mul, sub_zero,
    abs_of_nonneg (inner.boundaryDistance_nonneg vertex)] using hbound

/-- Points in distinct cells must both travel to their cell boundary. -/
theorem substitute_distinct_cell_boundary_separation
    (houter : ∀ vertex, outer.fullGraph.Reachable outer.source vertex)
    (hinner : ∀ vertex, inner.fullGraph.Reachable inner.source vertex)
    (first second : Fin outerEdges) (hdistinct : first ≠ second)
    (u v : Fin innerVertices) :
    inner.boundaryDistance u + inner.boundaryDistance v ≤
      ((outer.substitute inner).fullGraph.dist
        (Fintype.equivFin _ (outer.cellVertex inner first u))
        (Fintype.equivFin _ (outer.cellVertex inner second v)) : ℝ) := by
  let weight (edge : Fin outerEdges) : ℝ := if edge = first then 1 else if edge = second then -1 else 0
  have hweight (edge) : |weight edge| ≤ 1 := by
    dsimp only [weight]
    split_ifs <;> norm_num
  have hbound := outer.boundaryPotential_distance inner houter hinner weight hweight
    (outer.cellVertex inner first u) (outer.cellVertex inner second v)
  simpa only [boundaryPotential_cell, weight, if_true, if_neg hdistinct.symm,
    one_mul, neg_one_mul, sub_neg_eq_add,
    abs_of_nonneg (add_nonneg (inner.boundaryDistance_nonneg u) (inner.boundaryDistance_nonneg v))] using hbound

end
end Universality.FiniteNetwork

