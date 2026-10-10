import Universality.Graph.NetworkTowerConfiguration

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The coordinate at which an edge was first sampled. It is determined by
finitely many ancestral embeddings, with no choice from the infinite quotient. -/
def originCoordinate (tower : NetworkTower) :
    (n : ℕ) → Fin (tower.stage n).edges → Σ k, Fin (tower.stage k).edges
  | 0, e => ⟨0, e⟩
  | n + 1, e => Function.extend (tower.step n).edge (tower.originCoordinate n)
      (fun fresh => ⟨n + 1, fresh⟩) e

theorem originCoordinate_step (tower : NetworkTower) (n : ℕ) (e : Fin (tower.stage n).edges) :
    tower.originCoordinate (n + 1) ((tower.step n).edge e) = tower.originCoordinate n e :=
  (tower.step n).edge.injective.extend_apply _ _ e

theorem originCoordinate_fresh (tower : NetworkTower) (n : ℕ)
    (e : Fin (tower.stage (n + 1)).edges) (h : ¬ ∃ old, (tower.step n).edge old = e) :
    tower.originCoordinate (n + 1) e = ⟨n + 1, e⟩ :=
  Function.extend_apply' _ _ _ h

theorem edge_step (tower : NetworkTower) (n : ℕ) (e : Fin (tower.stage n).edges) :
    tower.edge (n + 1) ((tower.step n).edge e) = tower.edge n e := by
  simpa only [edgeMap, Nat.leRecOn_succ'] using
    tower.edge_map n (n + 1) (Nat.le_succ n) e

theorem edge_originCoordinate (tower : NetworkTower) (n : ℕ) (e : Fin (tower.stage n).edges) :
    tower.edge (tower.originCoordinate n e).1 (tower.originCoordinate n e).2 = tower.edge n e := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : ∃ old, (tower.step n).edge old = e
    · obtain ⟨old, rfl⟩ := h
      rw [tower.originCoordinate_step]
      exact (ih old).trans (tower.edge_step n old).symm
    · rw [tower.originCoordinate_fresh n e h]

theorem originCoordinate_injective (tower : NetworkTower) (n : ℕ) :
    Function.Injective (tower.originCoordinate n) := by
  intro e other heq
  apply tower.edge_injective n
  calc
    tower.edge n e = tower.edge (tower.originCoordinate n e).1 (tower.originCoordinate n e).2 :=
      (tower.edge_originCoordinate n e).symm
    _ = tower.edge (tower.originCoordinate n other).1 (tower.originCoordinate n other).2 :=
      congrArg (fun coordinate : Σ k, Fin (tower.stage k).edges =>
        tower.edge coordinate.1 coordinate.2) heq
    _ = tower.edge n other := tower.edge_originCoordinate n other

def originEmbedding (tower : NetworkTower) (n : ℕ) :
    Fin (tower.stage n).edges ↪ Σ k, Fin (tower.stage k).edges :=
  ⟨tower.originCoordinate n, tower.originCoordinate_injective n⟩

theorem originCoordinate_index_le (tower : NetworkTower) (n : ℕ)
    (e : Fin (tower.stage n).edges) : (tower.originCoordinate n e).1 ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    by_cases h : ∃ old, (tower.step n).edge old = e
    · obtain ⟨old, rfl⟩ := h
      rw [tower.originCoordinate_step]
      exact (ih old).trans (Nat.le_succ n)
    · rw [tower.originCoordinate_fresh n e h]


/-- Every actual finite-stage configuration is an injective selection from the
independent raw edge coordinates. This is the exact product-law interface. -/
theorem stageConfiguration_eq_origin (tower : NetworkTower)
    (fresh : ∀ n, FiniteNetwork.Configuration (tower.stage n).edges)
    (n : ℕ) (e : Fin (tower.stage n).edges) :
    tower.stageConfiguration fresh n e =
      fresh (tower.originCoordinate n e).1 (tower.originCoordinate n e).2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases h : ∃ old, (tower.step n).edge old = e
    · obtain ⟨old, rfl⟩ := h
      rw [tower.stageConfiguration_step, tower.originCoordinate_step]
      exact ih old
    · rw [tower.originCoordinate_fresh n e h]
      exact Function.extend_apply' _ _ _ h

end
end Universality.NetworkTower
