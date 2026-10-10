import Universality.Graph.RootClusterUnion

namespace Universality
noncomputable section

theorem finite_subset_monotone_union_stage {α : Type*} (clusters : ℕ → Finset α)
    (hmono : Monotone clusters) (vertices : Finset α)
    (hcover : ∀ x ∈ vertices, ∃ n, x ∈ clusters n) :
    ∃ n, vertices ⊆ clusters n := by
  classical
  revert hcover
  induction vertices using Finset.induction_on with
  | empty => exact fun _ => ⟨0, Finset.empty_subset _⟩
  | @insert x vertices hnot ih =>
    intro hcover
    obtain ⟨first, hfirst⟩ := hcover x (Finset.mem_insert_self _ _)
    obtain ⟨rest, hrest⟩ := ih (fun y hy => hcover y (Finset.mem_insert_of_mem hy))
    refine ⟨max first rest, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact hmono (le_max_left _ _) hfirst
    · exact hmono (le_max_right _ _) (hrest hy)

/-- The finite union-size event explicitly requires a finite set equal to the
union. Infinite unions do not satisfy the size-zero event. -/
def finiteUnionHasSize {α : Type*} (clusters : ℕ → Finset α) (size : ℕ) : Prop :=
  ∃ vertices : Finset α, (∀ x, x ∈ vertices ↔ ∃ n, x ∈ clusters n) ∧ vertices.card = size

theorem finiteUnionHasSize_iff_eventually_card {α : Type*} (clusters : ℕ → Finset α)
    (hmono : Monotone clusters) (size : ℕ) :
    finiteUnionHasSize clusters size ↔ ∃ first, ∀ n, first ≤ n → (clusters n).card = size := by
  classical
  constructor
  · rintro ⟨vertices, hvertices, hsize⟩
    obtain ⟨first, hfirst⟩ := finite_subset_monotone_union_stage clusters hmono vertices
      (fun x hx => (hvertices x).mp hx)
    refine ⟨first, fun n hn => ?_⟩
    have heq : clusters n = vertices := Finset.Subset.antisymm
      (fun x hx => (hvertices x).mpr ⟨n, hx⟩) (hfirst.trans (hmono hn))
    rwa [heq]
  · rintro ⟨first, hfirst⟩
    refine ⟨clusters first, ?_, hfirst first le_rfl⟩
    intro x
    constructor
    · exact fun hx => ⟨first, hx⟩
    · rintro ⟨n, hn⟩
      by_cases hle : n ≤ first
      · exact hmono hle hn
      · have hge : first ≤ n := le_of_lt (Nat.lt_of_not_ge hle)
        have heq : clusters first = clusters n := Finset.eq_of_subset_of_card_le
          (hmono hge) (by rw [hfirst n hge, hfirst first le_rfl])
        rwa [heq]

namespace NetworkTower
set_option backward.isDefEq.respectTransparency false

/-- The actual infinite graph has a finite rooted component with exactly the
specified number of vertices. The finiteness requirement is explicit. -/
def finiteClusterSizeEvent (tower : NetworkTower) (configuration : tower.Edge → Bool)
    (root : Fin (tower.stage 0).vertices) (size : ℕ) : Prop :=
  ∃ vertices : Finset tower.Vertex,
    (∀ x, x ∈ vertices ↔ (tower.openGraph configuration).Reachable (tower.vertex 0 root) x) ∧
      vertices.card = size

theorem finiteClusterSizeEvent_iff_eventually_card (tower : NetworkTower)
    (configuration : tower.Edge → Bool) (root : Fin (tower.stage 0).vertices) (size : ℕ) :
    tower.finiteClusterSizeEvent configuration root size ↔
      ∃ first, ∀ n, first ≤ n →
        ((tower.stage n).network.clusterVertices (tower.restrictConfiguration configuration n)
          (tower.vertexMap 0 n (Nat.zero_le n) root)).card = size := by
  have hunion (x : tower.Vertex) :
      (tower.openGraph configuration).Reachable (tower.vertex 0 root) x ↔
        ∃ n, x ∈ tower.rootClusterStage configuration root n := by
    simp only [tower.mem_rootClusterStage]
    exact tower.rooted_reachable_iff configuration root x
  have hevent : tower.finiteClusterSizeEvent configuration root size ↔
      finiteUnionHasSize (tower.rootClusterStage configuration root) size := by
    constructor
    · rintro ⟨vertices, hvertices, hsize⟩
      exact ⟨vertices, fun x => (hvertices x).trans (hunion x), hsize⟩
    · rintro ⟨vertices, hvertices, hsize⟩
      exact ⟨vertices, fun x => (hvertices x).trans (hunion x).symm, hsize⟩
  rw [hevent, finiteUnionHasSize_iff_eventually_card _
    (tower.rootClusterStage_monotone configuration root)]
  simp only [tower.rootClusterStage_card]

end NetworkTower
end
end Universality
