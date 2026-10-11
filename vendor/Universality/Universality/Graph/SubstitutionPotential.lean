import Universality.Graph.SubstitutionRadius

namespace Universality
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem graph_height_walk_bound {V : Type*} (G : SimpleGraph V)
    (height : V → ℝ) (hheight : ∀ {u v}, G.Adj u v → |height u - height v| ≤ 1)
    {u v : V} (walk : G.Walk u v) : |height u - height v| ≤ walk.length := by
  induction walk with
  | nil => simp
  | @cons u v w hadj walk ih =>
      have hstep := hheight hadj
      have htriangle := abs_add_le (height u - height v) (height v - height w)
      have heq : height u - height v + (height v - height w) = height u - height w := by ring
      rw [heq] at htriangle
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

theorem graph_height_distance_bound {V : Type*} (G : SimpleGraph V)
    (height : V → ℝ) (hheight : ∀ {u v}, G.Adj u v → |height u - height v| ≤ 1)
    {u v : V} (hconnected : G.Reachable u v) :
    |height u - height v| ≤ G.dist u v := by
  obtain ⟨walk, hlength⟩ := hconnected.exists_walk_length_eq_dist
  simpa only [hlength] using graph_height_walk_bound G height hheight walk

theorem graph_distance_height_adj {V : Type*} (G : SimpleGraph V)
    (root : V) {u v : V} (hadj : G.Adj u v) :
    |(G.dist root u : ℝ) - G.dist root v| ≤ 1 := by
  have hu := hadj.reachable.dist_triangle_right root
  have hv := hadj.symm.reachable.dist_triangle_right root
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at hu
  rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm] at hv
  have hu' : (G.dist root u : ℝ) ≤ G.dist root v + 1 := by exact_mod_cast hv
  have hv' : (G.dist root v : ℝ) ≤ G.dist root u + 1 := by exact_mod_cast hu
  rw [abs_le]
  constructor <;> linarith

theorem graph_iso_distance_of_reachable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (iso : G ≃g H) {u v : V} (hconnected : G.Reachable u v) :
    H.dist (iso u) (iso v) = G.dist u v := by
  obtain ⟨walk, hwalk⟩ := hconnected.exists_walk_length_eq_dist
  apply Nat.le_antisymm
  · have hbound := SimpleGraph.dist_le (walk.map iso.toHom)
    change H.dist (iso u) (iso v) ≤ (walk.map iso.toHom).length at hbound
    simpa only [SimpleGraph.Walk.length_map, hwalk] using hbound
  · obtain ⟨back, hback⟩ := (hconnected.map iso.toHom).exists_walk_length_eq_dist
    have hbound := SimpleGraph.dist_le (back.map iso.symm.toHom)
    rw [SimpleGraph.Walk.length_map, hback] at hbound
    change G.dist (iso.symm (iso u)) (iso.symm (iso v)) ≤ H.dist (iso u) (iso v) at hbound
    simpa only [RelIso.symm_apply_apply] using hbound

namespace FiniteNetwork
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

def substitutionPotential (coarse : Fin outerVertices → ℝ)
    (cellHeight : Fin outerEdges → Fin innerVertices → ℝ) : R.SubstitutionVertex S → ℝ
  | .inl vertex => coarse vertex
  | .inr (edge, vertex) => cellHeight edge vertex.val

theorem substitutionPotential_cell (coarse : Fin outerVertices → ℝ)
    (cellHeight : Fin outerEdges → Fin innerVertices → ℝ)
    (hsource : ∀ edge, cellHeight edge S.source = coarse (R.endpoint edge).1)
    (htarget : ∀ edge, cellHeight edge S.target = coarse (R.endpoint edge).2)
    (edge : Fin outerEdges) (vertex : Fin innerVertices) :
    R.substitutionPotential S coarse cellHeight (R.cellVertex S edge vertex) = cellHeight edge vertex := by
  by_cases hs : vertex = S.source
  · subst vertex
    rw [cellVertex_source]
    exact (hsource edge).symm
  · by_cases ht : vertex = S.target
    · subst vertex
      rw [cellVertex_target]
      exact (htarget edge).symm
    · simp only [cellVertex, dif_neg hs, dif_neg ht, substitutionPotential]

theorem substitutionPotential_adj (coarse : Fin outerVertices → ℝ)
    (cellHeight : Fin outerEdges → Fin innerVertices → ℝ)
    (hsource : ∀ edge, cellHeight edge S.source = coarse (R.endpoint edge).1)
    (htarget : ∀ edge, cellHeight edge S.target = coarse (R.endpoint edge).2)
    (hlocal : ∀ edge u v, S.fullGraph.Adj u v → |cellHeight edge u - cellHeight edge v| ≤ 1)
    {u v : R.SubstitutionVertex S}
    (hadj : (R.substitutedGraph S (fun _ _ => true)).Adj u v) :
    |R.substitutionPotential S coarse cellHeight u - R.substitutionPotential S coarse cellHeight v| ≤ 1 := by
  obtain ⟨_, edge, x, y, hadj, rfl, rfl⟩ := hadj
  rw [R.substitutionPotential_cell S coarse cellHeight hsource htarget,
    R.substitutionPotential_cell S coarse cellHeight hsource htarget]
  exact hlocal edge x y hadj

end FiniteNetwork
end
end Universality
