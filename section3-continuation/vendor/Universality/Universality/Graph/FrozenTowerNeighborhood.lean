import Universality.Graph.StageReachability

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem edge_step (tower : NetworkTower) (n : ℕ) (edge : Fin (tower.stage n).edges) :
    tower.edge (n + 1) ((tower.step n).edge edge) = tower.edge n edge := by
  simpa only [edgeMap, Nat.leRecOn_succ (Nat.le_refl n), Nat.leRecOn_self] using
    tower.edge_map n (n + 1) (Nat.le_succ n) edge

theorem restrictConfiguration_step (tower : NetworkTower) (configuration : tower.Edge → Bool) (n : ℕ) :
    (tower.step n).restrict (tower.restrictConfiguration configuration (n + 1)) =
      tower.restrictConfiguration configuration n := by
  funext edge
  exact congrArg configuration (tower.edge_step n edge)

/-- A finite stage containing every possible neighbor of one vertex controls
its neighborhood in the actual direct-limit graph. -/
theorem finite_neighborSet_of_stage_lifts (tower : NetworkTower)
    (configuration : tower.Edge → Bool) (n : ℕ) (root : Fin (tower.stage n).vertices)
    (hlift : ∀ (j : ℕ) (hnj : n ≤ j) (neighbor : Fin (tower.stage j).vertices),
      ((tower.stage j).network.openGraph (tower.restrictConfiguration configuration j)).Adj
        (tower.vertexMap n j hnj root) neighbor →
          ∃ vertex, tower.vertexMap n j hnj vertex = neighbor) :
    ((tower.openGraph configuration).neighborSet (tower.vertex n root)).Finite := by
  apply (Set.finite_range (tower.vertex n)).subset
  intro neighbor hadj
  obtain ⟨j, first, second, hroot, hneighbor, hstage⟩ :=
    tower.adjacency_from_stage configuration hadj
  obtain ⟨k, hnk, hjk, heq⟩ := tower.vertex_eq_at_stage hroot
  have hmapped := (tower.stageMapHom configuration j k hjk).map_rel' hstage
  change ((tower.stage k).network.openGraph (tower.restrictConfiguration configuration k)).Adj
    (tower.vertexMap j k hjk first) (tower.vertexMap j k hjk second) at hmapped
  rw [← heq] at hmapped
  obtain ⟨vertex, hvertex⟩ := hlift k hnk _ hmapped
  refine ⟨vertex, ?_⟩
  calc
    tower.vertex n vertex = tower.vertex k (tower.vertexMap n k hnk vertex) :=
      (tower.vertex_map n k hnk vertex).symm
    _ = tower.vertex k (tower.vertexMap j k hjk second) := congrArg (tower.vertex k) hvertex
    _ = tower.vertex j second := tower.vertex_map j k hjk second
    _ = neighbor := hneighbor.symm

def PreservesInterior (tower : NetworkTower) : Prop :=
  ∀ (n : ℕ) (vertex : (tower.stage n).network.InteriorVertex),
    (tower.step n).vertex vertex.val ≠ (tower.stage (n + 1)).network.source ∧
      (tower.step n).vertex vertex.val ≠ (tower.stage (n + 1)).network.target

def NoNewInteriorNeighbors (tower : NetworkTower) : Prop :=
  ∀ (n : ℕ) (vertex : (tower.stage n).network.InteriorVertex)
    (configuration : FiniteNetwork.Configuration (tower.stage (n + 1)).edges)
    (neighbor : Fin (tower.stage (n + 1)).vertices),
    ((tower.stage (n + 1)).network.openGraph configuration).Adj
      ((tower.step n).vertex vertex.val) neighbor →
    ∃ inside, (tower.step n).vertex inside = neighbor ∧
      ((tower.stage n).network.openGraph ((tower.step n).restrict configuration)).Adj vertex.val inside

theorem vertexMap_internal (tower : NetworkTower) (hpreserve : tower.PreservesInterior)
    (i j : ℕ) (hij : i ≤ j) (vertex : (tower.stage i).network.InteriorVertex) :
    tower.vertexMap i j hij vertex.val ≠ (tower.stage j).network.source ∧
      tower.vertexMap i j hij vertex.val ≠ (tower.stage j).network.target := by
  induction j, hij using Nat.le_induction with
  | base => simpa only [vertexMap, Nat.leRecOn_self] using vertex.property
  | succ j hij ih =>
    simpa only [vertexMap, Nat.leRecOn_succ hij] using
      hpreserve j ⟨tower.vertexMap i j hij vertex.val, ih⟩

theorem internal_neighbor_lifts (tower : NetworkTower) (hpreserve : tower.PreservesInterior)
    (hneighbors : tower.NoNewInteriorNeighbors) (configuration : tower.Edge → Bool)
    (i j : ℕ) (hij : i ≤ j) (vertex : (tower.stage i).network.InteriorVertex)
    (neighbor : Fin (tower.stage j).vertices)
    (hadj : ((tower.stage j).network.openGraph (tower.restrictConfiguration configuration j)).Adj
      (tower.vertexMap i j hij vertex.val) neighbor) :
    ∃ inside, tower.vertexMap i j hij inside = neighbor := by
  induction j, hij using Nat.le_induction with
  | base => exact ⟨neighbor, by simp only [vertexMap, Nat.leRecOn_self]⟩
  | succ j hij ih =>
    have hinternal := tower.vertexMap_internal hpreserve i j hij vertex
    simp only [vertexMap, Nat.leRecOn_succ hij] at hadj
    change ((tower.stage (j + 1)).network.openGraph
      (tower.restrictConfiguration configuration (j + 1))).Adj
      ((tower.step j).vertex (tower.vertexMap i j hij vertex.val)) neighbor at hadj
    obtain ⟨previous, hprevious, hpreviousAdj⟩ := hneighbors j
      ⟨tower.vertexMap i j hij vertex.val, hinternal⟩
      (tower.restrictConfiguration configuration (j + 1)) neighbor hadj
    rw [tower.restrictConfiguration_step] at hpreviousAdj
    obtain ⟨inside, hinside⟩ := ih previous hpreviousAdj
    refine ⟨inside, ?_⟩
    simp only [vertexMap, Nat.leRecOn_succ hij]
    change (tower.step j).vertex (tower.vertexMap i j hij inside) = neighbor
    rw [hinside]
    exact hprevious

theorem finite_neighborSet_of_internal (tower : NetworkTower) (hpreserve : tower.PreservesInterior)
    (hneighbors : tower.NoNewInteriorNeighbors) (configuration : tower.Edge → Bool)
    (n : ℕ) (vertex : (tower.stage n).network.InteriorVertex) :
    ((tower.openGraph configuration).neighborSet (tower.vertex n vertex.val)).Finite :=
  tower.finite_neighborSet_of_stage_lifts configuration n vertex.val
    (fun j hnj neighbor hadj =>
      tower.internal_neighbor_lifts hpreserve hneighbors configuration n j hnj vertex neighbor hadj)

def EventuallyInternal (tower : NetworkTower) : Prop :=
  ∀ (i : ℕ) (vertex : Fin (tower.stage i).vertices), ∃ (j : ℕ) (hij : i ≤ j),
    tower.vertexMap i j hij vertex ≠ (tower.stage j).network.source ∧
      tower.vertexMap i j hij vertex ≠ (tower.stage j).network.target

theorem finite_neighborSet_of_eventuallyInternal (tower : NetworkTower)
    (hpreserve : tower.PreservesInterior) (hneighbors : tower.NoNewInteriorNeighbors)
    (heventual : tower.EventuallyInternal) (configuration : tower.Edge → Bool)
    (vertex : tower.Vertex) : ((tower.openGraph configuration).neighborSet vertex).Finite := by
  obtain ⟨i, vertex, rfl⟩ := DirectLimit.exists_eq_mk tower.vertexEmbedding vertex
  obtain ⟨j, hij, hinternal⟩ := heventual i vertex
  change ((tower.openGraph configuration).neighborSet (tower.vertex i vertex)).Finite
  rw [← tower.vertex_map i j hij vertex]
  exact tower.finite_neighborSet_of_internal hpreserve hneighbors configuration j
    ⟨tower.vertexMap i j hij vertex, hinternal⟩

@[reducible] def locallyFiniteOfEventuallyInternal (tower : NetworkTower)
    (hpreserve : tower.PreservesInterior) (hneighbors : tower.NoNewInteriorNeighbors)
    (heventual : tower.EventuallyInternal) (configuration : tower.Edge → Bool) :
    (tower.openGraph configuration).LocallyFinite :=
  fun vertex => (tower.finite_neighborSet_of_eventuallyInternal
    hpreserve hneighbors heventual configuration vertex).fintype

end
end Universality.NetworkTower
