import Universality.Graph.DistanceCertificate

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : FiniteNetwork innerVertices innerEdges)

def substitutionHeight (outer : R.DistanceCertificate) (inner : S.DistanceCertificate) :
    R.SubstitutionVertex S → ℤ
  | .inl v => outer.height v * inner.length
  | .inr (edge, x) =>
      outer.height (R.endpoint edge).1 * inner.length +
        (outer.height (R.endpoint edge).2 - outer.height (R.endpoint edge).1) * inner.height x.val

theorem substitutionHeight_cell (outer : R.DistanceCertificate) (inner : S.DistanceCertificate)
    (edge : Fin outerEdges) (x : Fin innerVertices) :
    R.substitutionHeight S outer inner (R.cellVertex S edge x) =
      outer.height (R.endpoint edge).1 * inner.length +
        (outer.height (R.endpoint edge).2 - outer.height (R.endpoint edge).1) * inner.height x := by
  by_cases hs : x = S.source
  · subst x
    rw [cellVertex_source]
    simp [substitutionHeight, inner.source_height]
  · by_cases ht : x = S.target
    · subst x
      rw [cellVertex_target]
      simp only [substitutionHeight, inner.target_height]
      ring
    · simp only [cellVertex, dif_neg hs, dif_neg ht, substitutionHeight]

theorem substitutionHeight_edge_bound (outer : R.DistanceCertificate) (inner : S.DistanceCertificate)
    (edge : Fin outerEdges) (child : Fin innerEdges) :
    |R.substitutionHeight S outer inner (R.cellVertex S edge (S.endpoint child).1) -
      R.substitutionHeight S outer inner (R.cellVertex S edge (S.endpoint child).2)| ≤ 1 := by
  rw [substitutionHeight_cell, substitutionHeight_cell]
  have hfactor :
      outer.height (R.endpoint edge).1 * (inner.length : ℤ) +
          (outer.height (R.endpoint edge).2 - outer.height (R.endpoint edge).1) * inner.height (S.endpoint child).1 -
        (outer.height (R.endpoint edge).1 * (inner.length : ℤ) +
          (outer.height (R.endpoint edge).2 - outer.height (R.endpoint edge).1) * inner.height (S.endpoint child).2) =
      (outer.height (R.endpoint edge).2 - outer.height (R.endpoint edge).1) *
        (inner.height (S.endpoint child).1 - inner.height (S.endpoint child).2) := by ring
  rw [hfactor, abs_mul, abs_sub_comm (outer.height (R.endpoint edge).2)]
  have h := mul_le_mul (outer.edge_bound edge) (inner.edge_bound child)
    (abs_nonneg _) (by norm_num : (0 : ℤ) ≤ 1)
  simpa using h

theorem substituted_adj_walk_length (inner : S.DistanceCertificate)
    {u v : Fin outerVertices} (hadj : R.fullGraph.Adj u v) :
    ∃ walk : (R.substitutedGraph S (fun _ _ => true)).Walk (Sum.inl u) (Sum.inl v),
      walk.length = inner.length := by
  obtain ⟨_, edge, _, hpair | hpair⟩ := hadj
  · let walk := inner.walk.map (R.cellHom S (fun _ _ => true) edge)
    have hs : R.cellVertex S edge S.source = Sum.inl u := by rw [cellVertex_source, hpair]
    have ht : R.cellVertex S edge S.target = Sum.inl v := by rw [cellVertex_target, hpair]
    refine ⟨walk.copy hs ht, ?_⟩
    rw [SimpleGraph.Walk.length_copy]
    change (inner.walk.map (R.cellHom S (fun _ _ => true) edge)).length = inner.length
    rw [SimpleGraph.Walk.length_map]
    exact inner.walk_length
  · let walk := inner.walk.reverse.map (R.cellHom S (fun _ _ => true) edge)
    have hs : R.cellVertex S edge S.target = Sum.inl u := by rw [cellVertex_target, hpair]
    have ht : R.cellVertex S edge S.source = Sum.inl v := by rw [cellVertex_source, hpair]
    refine ⟨walk.copy hs ht, ?_⟩
    rw [SimpleGraph.Walk.length_copy]
    change (inner.walk.reverse.map (R.cellHom S (fun _ _ => true) edge)).length = inner.length
    rw [SimpleGraph.Walk.length_map]
    exact (SimpleGraph.Walk.length_reverse inner.walk).trans inner.walk_length

theorem substituted_walk_length (inner : S.DistanceCertificate)
    {u v : Fin outerVertices} (walk : R.fullGraph.Walk u v) :
    ∃ lifted : (R.substitutedGraph S (fun _ _ => true)).Walk (Sum.inl u) (Sum.inl v),
      lifted.length = walk.length * inner.length := by
  induction walk with
  | nil => exact ⟨.nil, by simp⟩
  | cons hadj walk ih =>
      obtain ⟨first, hfirst⟩ := R.substituted_adj_walk_length S inner hadj
      obtain ⟨rest, hrest⟩ := ih
      refine ⟨first.append rest, ?_⟩
      rw [SimpleGraph.Walk.length_append, hfirst, hrest, SimpleGraph.Walk.length_cons]
      ring

theorem substitute_walk_exists (outer : R.DistanceCertificate) (inner : S.DistanceCertificate) :
    ∃ walk : (R.substitute S).fullGraph.Walk (R.substitute S).source (R.substitute S).target,
      walk.length = outer.length * inner.length := by
  obtain ⟨walk, hlength⟩ := R.substituted_walk_length S inner outer.walk
  let mapped := walk.map (R.substitutionGraphIso S (fun _ _ => true)).toHom
  have hconfig : substitutionConfigurationEquiv (fun (_ : Fin outerEdges) (_ : Fin innerEdges) => true) =
      (fun _ => true) := rfl
  have hmapped : mapped.length = outer.length * inner.length := by
    simpa only [mapped, SimpleGraph.Walk.length_map, outer.walk_length] using hlength
  exact ⟨mapped, hmapped⟩

def DistanceCertificate.substitute (outer : R.DistanceCertificate) (inner : S.DistanceCertificate) :
    (R.substitute S).DistanceCertificate where
  length := outer.length * inner.length
  height v := R.substitutionHeight S outer inner ((Fintype.equivFin _).symm v)
  source_height := by
    change R.substitutionHeight S outer inner
      ((Fintype.equivFin _).symm (Fintype.equivFin _ (Sum.inl R.source))) = 0
    rw [Equiv.symm_apply_apply]
    simp [substitutionHeight, outer.source_height]
  target_height := by
    change R.substitutionHeight S outer inner
      ((Fintype.equivFin _).symm (Fintype.equivFin _ (Sum.inl R.target))) = _
    rw [Equiv.symm_apply_apply]
    simp [substitutionHeight, outer.target_height]
  edge_bound edge := by
    change |R.substitutionHeight S outer inner ((Fintype.equivFin _).symm
        (Fintype.equivFin _ (R.cellVertex S (finProdFinEquiv.symm edge).1
          (S.endpoint (finProdFinEquiv.symm edge).2).1))) -
      R.substitutionHeight S outer inner ((Fintype.equivFin _).symm
        (Fintype.equivFin _ (R.cellVertex S (finProdFinEquiv.symm edge).1
          (S.endpoint (finProdFinEquiv.symm edge).2).2)))| ≤ 1
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    exact R.substitutionHeight_edge_bound S outer inner _ _
  walk := Classical.choose (R.substitute_walk_exists S outer inner)
  walk_length := Classical.choose_spec (R.substitute_walk_exists S outer inner)

theorem substitute_terminal_distance
    (outer : R.fullGraph.Reachable R.source R.target)
    (inner : S.fullGraph.Reachable S.source S.target) :
    (R.substitute S).fullGraph.dist (R.substitute S).source (R.substitute S).target =
      R.fullGraph.dist R.source R.target * S.fullGraph.dist S.source S.target :=
  ((DistanceCertificate.ofReachable R outer).substitute R S
    (DistanceCertificate.ofReachable S inner)).distance_eq _

end
end Universality.FiniteNetwork
