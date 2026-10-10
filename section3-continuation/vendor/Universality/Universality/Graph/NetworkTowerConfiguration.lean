import Universality.Graph.DirectLimitGraph

namespace Universality.NetworkTower
noncomputable section

/-- Fresh independent coordinates may be supplied on every finite stage. The
recursive configuration retains the old child block and uses fresh coordinates
only on the complementary edges. -/
def stageConfiguration (tower : NetworkTower)
    (fresh : ∀ n, FiniteNetwork.Configuration (tower.stage n).edges) :
    ∀ n, FiniteNetwork.Configuration (tower.stage n).edges
  | 0 => fresh 0
  | n + 1 => Function.extend (tower.step n).edge (tower.stageConfiguration fresh n) (fresh (n + 1))

@[simp] theorem stageConfiguration_step (tower : NetworkTower)
    (fresh : ∀ n, FiniteNetwork.Configuration (tower.stage n).edges)
    (n : ℕ) (e : Fin (tower.stage n).edges) :
    tower.stageConfiguration fresh (n + 1) ((tower.step n).edge e) =
      tower.stageConfiguration fresh n e :=
  (tower.step n).edge.injective.extend_apply _ _ e

theorem stageConfiguration_map (tower : NetworkTower)
    (fresh : ∀ n, FiniteNetwork.Configuration (tower.stage n).edges)
    (i j : ℕ) (hij : i ≤ j) (e : Fin (tower.stage i).edges) :
    tower.stageConfiguration fresh j (tower.edgeMap i j hij e) =
      tower.stageConfiguration fresh i e := by
  induction j, hij using Nat.le_induction with
  | base => simp only [edgeMap, Nat.leRecOn_self]
  | succ j hij ih =>
    simp only [edgeMap, Nat.leRecOn_succ hij, stageConfiguration_step]
    exact ih

/-- A genuine configuration of the direct-limit graph, obtained from compatible
finite configurations rather than from a prescribed cluster-size law. -/
def configuration (tower : NetworkTower)
    (fresh : ∀ n, FiniteNetwork.Configuration (tower.stage n).edges) : tower.Edge → Bool :=
  DirectLimit.lift tower.edgeEmbedding (tower.stageConfiguration fresh)
    (fun i j hij e => (tower.stageConfiguration_map fresh i j hij e).symm)

@[simp] theorem configuration_edge (tower : NetworkTower)
    (fresh : ∀ n, FiniteNetwork.Configuration (tower.stage n).edges)
    (n : ℕ) (e : Fin (tower.stage n).edges) :
    tower.configuration fresh (tower.edge n e) = tower.stageConfiguration fresh n e := rfl

theorem restrict_configuration (tower : NetworkTower)
    (fresh : ∀ n, FiniteNetwork.Configuration (tower.stage n).edges) (n : ℕ) :
    tower.restrictConfiguration (tower.configuration fresh) n = tower.stageConfiguration fresh n := rfl

end
end Universality.NetworkTower


