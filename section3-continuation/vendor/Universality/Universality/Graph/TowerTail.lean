import Universality.Graph.FrozenTowerNeighborhood

namespace Universality.NetworkTower
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The same actual tower, viewed from a later finite stage. -/
def tail (tower : NetworkTower) (start : ℕ) : NetworkTower where
  stage n := tower.stage (start + n)
  step n := tower.step (start + n)

def RootEventuallyInternal (tower : NetworkTower) : Prop :=
  ∀ vertex : Fin (tower.stage 0).vertices, ∃ n,
    tower.vertexMap 0 n (Nat.zero_le n) vertex ≠ (tower.stage n).network.source ∧
    tower.vertexMap 0 n (Nat.zero_le n) vertex ≠ (tower.stage n).network.target

theorem tail_vertexMap (tower : NetworkTower) (start n : ℕ)
    (vertex : Fin (tower.stage start).vertices) :
    (tower.tail start).vertexMap 0 n (Nat.zero_le n) vertex =
      tower.vertexMap start (start + n) (Nat.le_add_right start n) vertex := by
  induction n with
  | zero => simp only [vertexMap, Nat.add_zero, Nat.leRecOn_self]
  | succ n ih =>
    simp only [vertexMap, Nat.add_succ, Nat.leRecOn_succ (Nat.zero_le n),
      Nat.leRecOn_succ (Nat.le_add_right start n)]
    change (tower.step (start + n)).vertex
      ((tower.tail start).vertexMap 0 n (Nat.zero_le n) vertex) =
      (tower.step (start + n)).vertex
        (tower.vertexMap start (start + n) (Nat.le_add_right start n) vertex)
    exact congrArg (tower.step (start + n)).vertex ih

theorem eventuallyInternal_of_tails (tower : NetworkTower)
    (htails : ∀ (start : ℕ) (vertex : Fin (tower.stage start).vertices), ∃ n,
      (tower.tail start).vertexMap 0 n (Nat.zero_le n) vertex ≠
          ((tower.tail start).stage n).network.source ∧
      (tower.tail start).vertexMap 0 n (Nat.zero_le n) vertex ≠
          ((tower.tail start).stage n).network.target) :
    tower.EventuallyInternal := by
  intro start vertex
  obtain ⟨n, hsource, htarget⟩ := htails start vertex
  rw [tower.tail_vertexMap start n vertex] at hsource htarget
  refine ⟨start + n, Nat.le_add_right start n, ?_, ?_⟩
  · exact hsource
  · exact htarget

end
end Universality.NetworkTower
