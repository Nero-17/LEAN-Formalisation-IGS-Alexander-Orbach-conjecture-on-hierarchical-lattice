import Universality.Graph.StageReachability

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Lifting a finite walk preserves its length, not merely reachability. -/
theorem walk_from_stage (tower : NetworkTower) (configuration : tower.Edge → Bool)
    {first last : tower.Vertex} (walk : (tower.openGraph configuration).Walk first last) :
    ∃ (n : ℕ) (start finish : Fin (tower.stage n).vertices),
      first = tower.vertex n start ∧ last = tower.vertex n finish ∧
      ∃ lifted : ((tower.stage n).network.openGraph
        (tower.restrictConfiguration configuration n)).Walk start finish,
        lifted.length = walk.length := by
  induction walk with
  | @nil first =>
    obtain ⟨n, start, rfl⟩ := DirectLimit.exists_eq_mk tower.vertexEmbedding first
    exact ⟨n, start, start, rfl, rfl, .nil, rfl⟩
  | @cons first middle last adjacency walk ih =>
    obtain ⟨i, start, next, hfirst, hmiddle, hadj⟩ := tower.adjacency_from_stage configuration adjacency
    obtain ⟨j, previous, finish, hmiddle', hlast, lifted, hlength⟩ := ih
    obtain ⟨k, hik, hjk, heq⟩ := tower.vertex_eq_at_stage (hmiddle.symm.trans hmiddle')
    have hstep := (tower.stageMapHom configuration i k hik).map_rel' hadj
    change ((tower.stage k).network.openGraph (tower.restrictConfiguration configuration k)).Adj
      (tower.vertexMap i k hik start) (tower.vertexMap i k hik next) at hstep
    rw [heq] at hstep
    refine ⟨k, tower.vertexMap i k hik start, tower.vertexMap j k hjk finish,
      hfirst.trans (tower.vertex_map i k hik start).symm,
      hlast.trans (tower.vertex_map j k hjk finish).symm,
      .cons hstep (lifted.map (tower.stageMapHom configuration j k hjk)), ?_⟩
    simp only [SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_map, hlength]

theorem vertex_eq_at_every_later_stage (tower : NetworkTower) {i j : ℕ}
    {first : Fin (tower.stage i).vertices} {second : Fin (tower.stage j).vertices}
    (heq : tower.vertex i first = tower.vertex j second) :
    ∃ n, ∀ k, n ≤ k → ∃ (hik : i ≤ k) (hjk : j ≤ k),
      tower.vertexMap i k hik first = tower.vertexMap j k hjk second := by
  obtain ⟨n, hin, hjn, heq⟩ := tower.vertex_eq_at_stage heq
  refine ⟨n, fun k hnk => ⟨hin.trans hnk, hjn.trans hnk, ?_⟩⟩
  have hfirst := DirectedSystem.map_map (f := fun i j hij => tower.vertexMap i j hij) hin hnk first
  have hsecond := DirectedSystem.map_map (f := fun i j hij => tower.vertexMap i j hij) hjn hnk second
  rw [← hfirst, ← hsecond, heq]

/-- A path whose endpoints have already been specified at one stage lifts to
a later stage with those same transported endpoints and the same length. -/
theorem walk_from_stage_fixedEndpoints (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (i : ℕ) (first last : Fin (tower.stage i).vertices)
    (walk : (tower.openGraph configuration).Walk (tower.vertex i first) (tower.vertex i last)) :
    ∃ (k : ℕ) (hik : i ≤ k),
      ∃ lifted : ((tower.stage k).network.openGraph
        (tower.restrictConfiguration configuration k)).Walk
          (tower.vertexMap i k hik first) (tower.vertexMap i k hik last),
        lifted.length = walk.length := by
  obtain ⟨j, start, finish, hfirst, hlast, lifted, hlength⟩ := tower.walk_from_stage configuration walk
  obtain ⟨firstBound, hfirstBound⟩ := tower.vertex_eq_at_every_later_stage hfirst
  obtain ⟨lastBound, hlastBound⟩ := tower.vertex_eq_at_every_later_stage hlast
  let k := max firstBound lastBound
  obtain ⟨hik, hjk, hfirstEq⟩ := hfirstBound k (Nat.le_max_left _ _)
  obtain ⟨_, _, hlastEq⟩ := hlastBound k (Nat.le_max_right _ _)
  refine ⟨k, hik, ?_⟩
  rw [hfirstEq, hlastEq]
  exact ⟨lifted.map (tower.stageMapHom configuration j k hjk),
    by simpa only [SimpleGraph.Walk.length_map] using hlength⟩

end
end Universality.NetworkTower
