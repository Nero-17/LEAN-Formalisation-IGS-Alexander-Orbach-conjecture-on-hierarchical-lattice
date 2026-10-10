import Universality.Graph.SubstitutionPotential

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- Extend a one-Lipschitz potential from one cell to the whole substituted
graph. Other cells interpolate their two boundary values at terminal scale. -/
theorem exists_cell_potential_extension
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (edge : Fin outerEdges) (height : Fin innerVertices → ℝ)
    (hheight : ∀ {u v}, S.fullGraph.Adj u v → |height u - height v| ≤ 1) :
    ∃ extension : R.SubstitutionVertex S → ℝ,
      (∀ vertex, extension (R.cellVertex S edge vertex) = height vertex) ∧
      (∀ {u v}, (R.substitutedGraph S (fun _ _ => true)).Adj u v →
        |extension u - extension v| ≤ 1) := by
  let coarse : Fin outerVertices → ℝ := fun vertex =>
    if vertex = (R.endpoint edge).2 then height S.target else height S.source
  have hsource : coarse (R.endpoint edge).1 = height S.source := by
    simp only [coarse, if_neg (R.loopless edge)]
  have htarget : coarse (R.endpoint edge).2 = height S.target := by simp [coarse]
  have hterminal := graph_height_distance_bound S.fullGraph height hheight (hinner S.target)
  have hlength : (0 : ℝ) < S.fullGraph.dist S.source S.target := by
    have hne : S.fullGraph.dist S.source S.target ≠ 0 := by
      intro hz
      exact S.terminals_distinct ((hinner S.target).dist_eq_zero_iff.mp hz)
    exact_mod_cast Nat.pos_of_ne_zero hne
  have hcoarse (other : Fin outerEdges) :
      |coarse (R.endpoint other).2 - coarse (R.endpoint other).1| ≤
        S.fullGraph.dist S.source S.target := by
    dsimp only [coarse]
    split_ifs <;> first | simpa only [sub_self, abs_zero] using hlength.le |
      simpa only [abs_sub_comm] using hterminal
  let cellHeight : Fin outerEdges → Fin innerVertices → ℝ := fun other vertex =>
    if other = edge then height vertex else coarse (R.endpoint other).1 +
      (coarse (R.endpoint other).2 - coarse (R.endpoint other).1) /
        (S.fullGraph.dist S.source S.target : ℝ) * S.fullGraph.dist S.source vertex
  have hlocalSource (other : Fin outerEdges) : cellHeight other S.source = coarse (R.endpoint other).1 := by
    by_cases heq : other = edge
    · subst other
      simp [cellHeight, hsource]
    · simp [cellHeight, heq]
  have hlocalTarget (other : Fin outerEdges) : cellHeight other S.target = coarse (R.endpoint other).2 := by
    by_cases heq : other = edge
    · subst other
      simp [cellHeight, htarget]
    · dsimp only [cellHeight]
      rw [if_neg heq, div_mul_cancel₀ _ hlength.ne']
      ring
  have hlocal (other : Fin outerEdges) (u v : Fin innerVertices)
      (hadj : S.fullGraph.Adj u v) : |cellHeight other u - cellHeight other v| ≤ 1 := by
    by_cases heq : other = edge
    · simpa only [cellHeight, if_pos heq] using hheight hadj
    · have hfactor : |(coarse (R.endpoint other).2 - coarse (R.endpoint other).1) /
          (S.fullGraph.dist S.source S.target : ℝ)| ≤ 1 := by
        rw [abs_div, abs_of_pos hlength, div_le_one hlength]
        exact hcoarse other
      have hdistance := graph_distance_height_adj S.fullGraph S.source hadj
      have hequality : cellHeight other u - cellHeight other v =
          ((coarse (R.endpoint other).2 - coarse (R.endpoint other).1) /
            (S.fullGraph.dist S.source S.target : ℝ)) *
              ((S.fullGraph.dist S.source u : ℝ) - S.fullGraph.dist S.source v) := by
        simp only [cellHeight, if_neg heq]
        ring
      rw [hequality, abs_mul]
      simpa only [one_mul] using mul_le_mul hfactor hdistance (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
  refine ⟨R.substitutionPotential S coarse cellHeight, ?_, ?_⟩
  · intro vertex
    rw [R.substitutionPotential_cell S coarse cellHeight hlocalSource hlocalTarget]
    simp only [cellHeight, if_pos rfl]
  · exact R.substitutionPotential_adj S coarse cellHeight hlocalSource hlocalTarget hlocal

/-- A cell is isometrically embedded in the actual substituted graph,
including when the outer graph offers alternative paths between terminals. -/
theorem substituted_cell_distance
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (edge : Fin outerEdges) (u v : Fin innerVertices) :
    (R.substitutedGraph S (fun _ _ => true)).dist
      (R.cellVertex S edge u) (R.cellVertex S edge v) = S.fullGraph.dist u v := by
  have hconnected := (hinner u).symm.trans (hinner v)
  obtain ⟨walk, hwalk⟩ := hconnected.exists_walk_length_eq_dist
  let hlifted := walk.map (R.cellHom S (fun _ _ => true) edge)
  apply Nat.le_antisymm
  · have hbound := SimpleGraph.dist_le hlifted
    change (R.substitutedGraph S (fun _ _ => true)).dist
      (R.cellVertex S edge u) (R.cellVertex S edge v) ≤ hlifted.length at hbound
    simpa only [hlifted, SimpleGraph.Walk.length_map, hwalk] using hbound
  · obtain ⟨height, hrestriction, hheight⟩ := R.exists_cell_potential_extension S hinner edge
      (fun vertex => (S.fullGraph.dist u vertex : ℝ)) (graph_distance_height_adj S.fullGraph u)
    have hbound := graph_height_distance_bound _ height hheight ⟨hlifted⟩
    change |height (R.cellVertex S edge u) - height (R.cellVertex S edge v)| ≤
      ((R.substitutedGraph S (fun _ _ => true)).dist
        (R.cellVertex S edge u) (R.cellVertex S edge v) : ℝ) at hbound
    rw [hrestriction u, hrestriction v] at hbound
    simp only [SimpleGraph.dist_self, Nat.cast_zero, zero_sub, abs_neg] at hbound
    rw [abs_of_nonneg (show (0 : ℝ) ≤ S.fullGraph.dist u v by positivity)] at hbound
    exact_mod_cast hbound

theorem substitute_cell_distance
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (edge : Fin outerEdges) (u v : Fin innerVertices) :
    (R.substitute S).fullGraph.dist
      (Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge u))
      (Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S edge v)) =
      S.fullGraph.dist u v := by
  have hconnected := ((hinner u).symm.trans (hinner v)).map
    (R.cellHom S (fun _ _ => true) edge)
  exact (graph_iso_distance_of_reachable (R.substitutionGraphIso S (fun _ _ => true))
    hconnected).trans (R.substituted_cell_distance S hinner edge u v)

end
end Universality.FiniteNetwork
