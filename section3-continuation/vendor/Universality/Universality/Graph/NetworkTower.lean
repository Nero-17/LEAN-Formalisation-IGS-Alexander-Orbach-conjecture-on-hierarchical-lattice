import Universality.Graph.GenerationCellEmbedding
import Mathlib.Order.DirectedInverseSystem

namespace Universality
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- An increasing sequence of actual finite indexed networks. -/
structure NetworkTower where
  stage : ℕ → Rule
  step : ∀ n, (stage n).network.NetworkEmbedding (stage (n + 1)).network

namespace NetworkTower

def vertexMap (tower : NetworkTower) (i j : ℕ) (hij : i ≤ j) :
    Fin (tower.stage i).vertices → Fin (tower.stage j).vertices :=
  Nat.leRecOn hij (fun {n} => (tower.step n).vertex)

def edgeMap (tower : NetworkTower) (i j : ℕ) (hij : i ≤ j) :
    Fin (tower.stage i).edges → Fin (tower.stage j).edges :=
  Nat.leRecOn hij (fun {n} => (tower.step n).edge)

instance vertexSystem (tower : NetworkTower) :
    DirectedSystem (fun n => Fin (tower.stage n).vertices) (tower.vertexMap · · ·) where
  map_self := by
    intro i x
    exact Nat.leRecOn_self (C := fun n => Fin (tower.stage n).vertices)
      (next := fun {n} => (tower.step n).vertex) x
  map_map := by
    intro k j i hij hjk x
    exact (Nat.leRecOn_trans (C := fun n => Fin (tower.stage n).vertices)
      (next := fun {n} => (tower.step n).vertex) hij hjk x).symm

instance edgeSystem (tower : NetworkTower) :
    DirectedSystem (fun n => Fin (tower.stage n).edges) (tower.edgeMap · · ·) where
  map_self := by
    intro i x
    exact Nat.leRecOn_self (C := fun n => Fin (tower.stage n).edges)
      (next := fun {n} => (tower.step n).edge) x
  map_map := by
    intro k j i hij hjk x
    exact (Nat.leRecOn_trans (C := fun n => Fin (tower.stage n).edges)
      (next := fun {n} => (tower.step n).edge) hij hjk x).symm

theorem vertexMap_injective (tower : NetworkTower) (i j : ℕ) (hij : i ≤ j) :
    Function.Injective (tower.vertexMap i j hij) := by
  induction j, hij using Nat.le_induction with
  | base =>
    intro x y heq
    simpa only [vertexMap, Nat.leRecOn_self] using heq
  | succ j hij ih =>
    intro x y heq
    simp only [vertexMap, Nat.leRecOn_succ hij] at heq
    exact ih ((tower.step j).vertex.injective heq)

theorem edgeMap_injective (tower : NetworkTower) (i j : ℕ) (hij : i ≤ j) :
    Function.Injective (tower.edgeMap i j hij) := by
  induction j, hij using Nat.le_induction with
  | base =>
    intro x y heq
    simpa only [edgeMap, Nat.leRecOn_self] using heq
  | succ j hij ih =>
    intro x y heq
    simp only [edgeMap, Nat.leRecOn_succ hij] at heq
    exact ih ((tower.step j).edge.injective heq)

theorem map_endpoint (tower : NetworkTower) (i j : ℕ) (hij : i ≤ j)
    (edge : Fin (tower.stage i).edges) :
    (tower.stage j).network.endpoint (tower.edgeMap i j hij edge) =
      (tower.vertexMap i j hij ((tower.stage i).network.endpoint edge).1,
       tower.vertexMap i j hij ((tower.stage i).network.endpoint edge).2) := by
  induction j, hij using Nat.le_induction with
  | base => simp only [edgeMap, vertexMap, Nat.leRecOn_self]
  | succ j hij ih =>
    simp only [edgeMap, vertexMap, Nat.leRecOn_succ hij]
    rw [(tower.step j).endpoint]
    change ((tower.step j).vertex ((tower.stage j).network.endpoint
        (tower.edgeMap i j hij edge)).1,
      (tower.step j).vertex ((tower.stage j).network.endpoint
        (tower.edgeMap i j hij edge)).2) = _
    rw [ih]
    rfl

def vertexEmbedding (tower : NetworkTower) (i j : ℕ) (hij : i ≤ j) :
    Fin (tower.stage i).vertices ↪ Fin (tower.stage j).vertices :=
  ⟨tower.vertexMap i j hij, tower.vertexMap_injective i j hij⟩

def edgeEmbedding (tower : NetworkTower) (i j : ℕ) (hij : i ≤ j) :
    Fin (tower.stage i).edges ↪ Fin (tower.stage j).edges :=
  ⟨tower.edgeMap i j hij, tower.edgeMap_injective i j hij⟩

instance vertexEmbeddingSystem (tower : NetworkTower) :
    DirectedSystem (fun n => Fin (tower.stage n).vertices)
      (fun i j hij => tower.vertexEmbedding i j hij) := tower.vertexSystem

instance edgeEmbeddingSystem (tower : NetworkTower) :
    DirectedSystem (fun n => Fin (tower.stage n).edges)
      (fun i j hij => tower.edgeEmbedding i j hij) := tower.edgeSystem

def Vertex (tower : NetworkTower) :=
  DirectLimit (fun n => Fin (tower.stage n).vertices) tower.vertexEmbedding

def Edge (tower : NetworkTower) :=
  DirectLimit (fun n => Fin (tower.stage n).edges) tower.edgeEmbedding

def vertex (tower : NetworkTower) (n : ℕ) (x : Fin (tower.stage n).vertices) : tower.Vertex :=
  ⟦⟨n, x⟩⟧

def edge (tower : NetworkTower) (n : ℕ) (e : Fin (tower.stage n).edges) : tower.Edge :=
  ⟦⟨n, e⟩⟧

theorem vertex_injective (tower : NetworkTower) (n : ℕ) : Function.Injective (tower.vertex n) :=
  DirectLimit.mk_injective tower.vertexEmbedding tower.vertexMap_injective n

theorem edge_injective (tower : NetworkTower) (n : ℕ) : Function.Injective (tower.edge n) :=
  DirectLimit.mk_injective tower.edgeEmbedding tower.edgeMap_injective n

@[simp] theorem vertex_map (tower : NetworkTower) (i j : ℕ) (hij : i ≤ j)
    (x : Fin (tower.stage i).vertices) :
    tower.vertex j (tower.vertexMap i j hij x) = tower.vertex i x :=
  DirectLimit.mk_apply (F := fun n => Fin (tower.stage n).vertices)
    (f := tower.vertexEmbedding) i j x hij

@[simp] theorem edge_map (tower : NetworkTower) (i j : ℕ) (hij : i ≤ j)
    (e : Fin (tower.stage i).edges) :
    tower.edge j (tower.edgeMap i j hij e) = tower.edge i e :=
  DirectLimit.mk_apply (F := fun n => Fin (tower.stage n).edges)
    (f := tower.edgeEmbedding) i j e hij

end NetworkTower

/-- The outward ancestral tower at a fixed root age and infinite edge address. -/
def Rule.ancestralTower (rule : Rule) (age : ℕ) (address : ℕ → Fin rule.edges) : NetworkTower where
  stage n := rule.generation (age + n)
  step n := (Nat.add_assoc age n 1) ▸ rule.generationCellEmbedding (age + n) (address n)

end
end Universality

