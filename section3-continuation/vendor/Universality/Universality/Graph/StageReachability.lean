import Universality.Graph.DirectLimitGraph

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

def stageMapHom (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (i j : ℕ) (hij : i ≤ j) :
    (tower.stage i).network.openGraph (tower.restrictConfiguration configuration i) →g
      (tower.stage j).network.openGraph (tower.restrictConfiguration configuration j) where
  toFun := tower.vertexMap i j hij
  map_rel' := by
    intro x y h
    rcases h with ⟨hne, e, hopen, hpair | hpair⟩
    · refine ⟨fun heq => hne (tower.vertexMap_injective i j hij heq),
        tower.edgeMap i j hij e, ?_, Or.inl ?_⟩
      · change configuration (tower.edge j (tower.edgeMap i j hij e)) = true
        rw [tower.edge_map]
        exact hopen
      · rw [tower.map_endpoint, hpair]
    · refine ⟨fun heq => hne (tower.vertexMap_injective i j hij heq),
        tower.edgeMap i j hij e, ?_, Or.inr ?_⟩
      · change configuration (tower.edge j (tower.edgeMap i j hij e)) = true
        rw [tower.edge_map]
        exact hopen
      · rw [tower.map_endpoint, hpair]

theorem vertex_eq_at_stage (tower : NetworkTower) {i j : ℕ}
    {x : Fin (tower.stage i).vertices} {y : Fin (tower.stage j).vertices}
    (heq : tower.vertex i x = tower.vertex j y) :
    ∃ (k : ℕ) (hik : i ≤ k) (hjk : j ≤ k),
      tower.vertexMap i k hik x = tower.vertexMap j k hjk y :=
  Quotient.eq.mp heq

/-- Finite paths in the actual direct-limit graph lift to one common finite
stage. This is proved from edge representatives and directedness. -/
theorem reachable_from_stage (tower : NetworkTower) (configuration : tower.Edge → Bool)
    {x y : tower.Vertex} (h : (tower.openGraph configuration).Reachable x y) :
    ∃ (n : ℕ) (u v : Fin (tower.stage n).vertices),
      x = tower.vertex n u ∧ y = tower.vertex n v ∧
      ((tower.stage n).network.openGraph (tower.restrictConfiguration configuration n)).Reachable u v := by
  rcases h with ⟨walk⟩
  induction walk with
  | @nil x =>
    obtain ⟨n, u, rfl⟩ := DirectLimit.exists_eq_mk tower.vertexEmbedding x
    exact ⟨n, u, u, rfl, rfl, .refl u⟩
  | @cons x middle y adjacency walk ih =>
    obtain ⟨i, u, v, hx, hmiddle, hadj⟩ := tower.adjacency_from_stage configuration adjacency
    obtain ⟨j, w, z, hmiddle', hy, hreach⟩ := ih
    obtain ⟨k, hik, hjk, heq⟩ := tower.vertex_eq_at_stage (hmiddle.symm.trans hmiddle')
    refine ⟨k, tower.vertexMap i k hik u, tower.vertexMap j k hjk z,
      hx.trans (tower.vertex_map i k hik u).symm,
      hy.trans (tower.vertex_map j k hjk z).symm, ?_⟩
    have hfirst : ((tower.stage k).network.openGraph
        (tower.restrictConfiguration configuration k)).Reachable
        (tower.vertexMap i k hik u) (tower.vertexMap i k hik v) :=
      hadj.reachable.map (tower.stageMapHom configuration i k hik)
    have hrest : ((tower.stage k).network.openGraph
        (tower.restrictConfiguration configuration k)).Reachable
        (tower.vertexMap j k hjk w) (tower.vertexMap j k hjk z) :=
      hreach.map (tower.stageMapHom configuration j k hjk)
    rw [heq] at hfirst
    exact hfirst.trans hrest

/-- The cluster rooted at stage zero is exactly the union of its finite-stage
clusters, with the root transported by the actual vertex embeddings. -/
theorem rooted_reachable_iff (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (root : Fin (tower.stage 0).vertices) (x : tower.Vertex) :
    (tower.openGraph configuration).Reachable (tower.vertex 0 root) x ↔
      ∃ (n : ℕ) (v : Fin (tower.stage n).vertices), x = tower.vertex n v ∧
        ((tower.stage n).network.openGraph (tower.restrictConfiguration configuration n)).Reachable
          (tower.vertexMap 0 n (Nat.zero_le n) root) v := by
  constructor
  · intro h
    obtain ⟨i, u, v, hroot, hx, hreach⟩ := tower.reachable_from_stage configuration h
    obtain ⟨n, hzero, hin, heq⟩ := tower.vertex_eq_at_stage hroot
    refine ⟨n, tower.vertexMap i n hin v, hx.trans (tower.vertex_map i n hin v).symm, ?_⟩
    have hmapped : ((tower.stage n).network.openGraph
        (tower.restrictConfiguration configuration n)).Reachable
        (tower.vertexMap i n hin u) (tower.vertexMap i n hin v) :=
      hreach.map (tower.stageMapHom configuration i n hin)
    rwa [← heq] at hmapped
  · rintro ⟨n, v, rfl, hreach⟩
    have hmapped := hreach.map (tower.stageOpenGraphHom configuration n)
    change (tower.openGraph configuration).Reachable
      (tower.vertex n (tower.vertexMap 0 n (Nat.zero_le n) root)) (tower.vertex n v) at hmapped
    rwa [tower.vertex_map] at hmapped

end
end Universality.NetworkTower
