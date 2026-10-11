import Universality.Graph.NetworkTower

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Endpoints are inherited from the finite stage containing the edge. -/
def endpoint (tower : NetworkTower) : tower.Edge → tower.Vertex × tower.Vertex :=
  DirectLimit.lift tower.edgeEmbedding
    (fun n e => (tower.vertex n ((tower.stage n).network.endpoint e).1,
      tower.vertex n ((tower.stage n).network.endpoint e).2))
    (by
      intro i j hij e
      change (tower.vertex i ((tower.stage i).network.endpoint e).1,
        tower.vertex i ((tower.stage i).network.endpoint e).2) =
        (tower.vertex j ((tower.stage j).network.endpoint (tower.edgeMap i j hij e)).1,
         tower.vertex j ((tower.stage j).network.endpoint (tower.edgeMap i j hij e)).2)
      rw [tower.map_endpoint i j hij e]
      simp only [tower.vertex_map])

@[simp] theorem endpoint_edge (tower : NetworkTower) (n : ℕ)
    (e : Fin (tower.stage n).edges) :
    tower.endpoint (tower.edge n e) =
      (tower.vertex n ((tower.stage n).network.endpoint e).1,
       tower.vertex n ((tower.stage n).network.endpoint e).2) := rfl

theorem endpoint_distinct (tower : NetworkTower) (e : tower.Edge) :
    (tower.endpoint e).1 ≠ (tower.endpoint e).2 := by
  induction e using DirectLimit.induction tower.edgeEmbedding with
  | ih n e =>
    exact fun heq => (tower.stage n).network.loopless e (tower.vertex_injective n heq)

def openGraph (tower : NetworkTower) (configuration : tower.Edge → Bool) :
    SimpleGraph tower.Vertex where
  Adj x y := x ≠ y ∧ ∃ e, configuration e = true ∧
    (tower.endpoint e = (x, y) ∨ tower.endpoint e = (y, x))
  symm := ⟨by
    intro x y h
    rcases h with ⟨hne, e, hopen, hpair | hpair⟩
    · exact ⟨hne.symm, e, hopen, Or.inr hpair⟩
    · exact ⟨hne.symm, e, hopen, Or.inl hpair⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

def restrictConfiguration (tower : NetworkTower) (configuration : tower.Edge → Bool) (n : ℕ) :
    FiniteNetwork.Configuration (tower.stage n).edges := fun e => configuration (tower.edge n e)

/-- Every finite stage embeds into the actual percolated infinite graph. -/
def stageOpenGraphHom (tower : NetworkTower) (configuration : tower.Edge → Bool) (n : ℕ) :
    (tower.stage n).network.openGraph (tower.restrictConfiguration configuration n) →g
      tower.openGraph configuration where
  toFun := tower.vertex n
  map_rel' := by
    intro x y h
    rcases h with ⟨hne, e, hopen, hpair | hpair⟩
    · refine ⟨fun heq => hne (tower.vertex_injective n heq), tower.edge n e, hopen,
        Or.inl ?_⟩
      rw [tower.endpoint_edge, hpair]
    · refine ⟨fun heq => hne (tower.vertex_injective n heq), tower.edge n e, hopen,
        Or.inr ?_⟩
      rw [tower.endpoint_edge, hpair]

/-- Any open edge of the limit graph already occurs in a finite stage. -/
theorem adjacency_from_stage (tower : NetworkTower) (configuration : tower.Edge → Bool)
    {x y : tower.Vertex} (h : (tower.openGraph configuration).Adj x y) :
    ∃ (n : ℕ) (u v : Fin (tower.stage n).vertices),
      x = tower.vertex n u ∧ y = tower.vertex n v ∧
      ((tower.stage n).network.openGraph (tower.restrictConfiguration configuration n)).Adj u v := by
  rcases h with ⟨_, edge, hopen, hpair⟩
  obtain ⟨n, e, rfl⟩ := DirectLimit.exists_eq_mk tower.edgeEmbedding edge
  change configuration (tower.edge n e) = true at hopen
  change tower.endpoint (tower.edge n e) = (x, y) ∨
    tower.endpoint (tower.edge n e) = (y, x) at hpair
  rw [tower.endpoint_edge] at hpair
  rcases hpair with hpair | hpair
  · refine ⟨n, ((tower.stage n).network.endpoint e).1,
      ((tower.stage n).network.endpoint e).2,
      (congrArg Prod.fst hpair).symm, (congrArg Prod.snd hpair).symm, ?_⟩
    exact ⟨(tower.stage n).network.loopless e, e, hopen, Or.inl rfl⟩
  · refine ⟨n, ((tower.stage n).network.endpoint e).2,
      ((tower.stage n).network.endpoint e).1,
      (congrArg Prod.snd hpair).symm, (congrArg Prod.fst hpair).symm, ?_⟩
    exact ⟨((tower.stage n).network.loopless e).symm, e, hopen, Or.inr rfl⟩

end
end Universality.NetworkTower


