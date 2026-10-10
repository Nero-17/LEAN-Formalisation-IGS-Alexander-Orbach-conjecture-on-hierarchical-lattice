import Universality.Graph.CrossingOpenCount
import Universality.Graph.PathEdgeMinimality

namespace Universality.FiniteNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem openGraph_le_full (configuration : Configuration edges) : R.openGraph configuration ≤ R.fullGraph := by
  intro first second hadj
  obtain ⟨hne, edge, _, hpair⟩ := hadj
  exact ⟨hne, edge, rfl, hpair⟩

theorem edge_open_of_mem_walk
    (hsimple : Function.Injective (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2)))
    (configuration : Configuration edges) {source target : Fin vertices}
    (walk : (R.openGraph configuration).Walk source target) (edge : Fin edges)
    (hmem : s((R.endpoint edge).1, (R.endpoint edge).2) ∈ walk.edges) : configuration edge = true := by
  have hpair := SimpleGraph.mem_edgeFinset.mpr (walk.edges_subset_edgeSet hmem)
  rw [R.openGraph_edgeFinset] at hpair
  obtain ⟨other, hopen, heq⟩ := Finset.mem_image.mp hpair
  have heq := hsimple heq
  subst other
  exact (Finset.mem_filter.mp hopen).2

theorem exists_pivotal_of_path
    (hsimple : Function.Injective (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2)))
    (edge : Fin edges) (walk : R.fullGraph.Walk R.source R.target)
    (hpath : walk.IsPath) (hmem : s((R.endpoint edge).1, (R.endpoint edge).2) ∈ walk.edges) :
    ∃ configuration, R.pivotal configuration edge = true := by
  classical
  let configuration : Configuration edges := fun other => decide (s((R.endpoint other).1, (R.endpoint other).2) ∈ walk.edges)
  have hexists (pair : Sym2 (Fin vertices)) (hpair : pair ∈ walk.edges) :
      ∃ other, configuration other = true ∧ s((R.endpoint other).1, (R.endpoint other).2) = pair := by
    have hfull := SimpleGraph.mem_edgeFinset.mpr (walk.edges_subset_edgeSet hpair)
    change pair ∈ (R.openGraph (fun _ => true)).edgeFinset at hfull
    rw [R.openGraph_edgeFinset] at hfull
    obtain ⟨other, _, heq⟩ := Finset.mem_image.mp hfull
    exact ⟨other, by simp [configuration, heq, hpair], heq⟩
  have hcross : R.crosses configuration = true :=
    (R.crosses_eq_true _).mpr (R.reachable_of_walk_edges_open configuration walk hexists)
  have hopen : Function.update configuration edge true = configuration := by
    apply Function.update_eq_self_iff.mpr
    simp [configuration, hmem]
  have hclosed : R.crosses (Function.update configuration edge false) = false := by
    cases hresult : R.crosses (Function.update configuration edge false) with
    | false => rfl
    | true =>
      obtain ⟨other, hother, _⟩ := ((R.crosses_eq_true _).mp hresult).exists_path_of_dist
      have hsubset : (other.mapLe (R.openGraph_le_full _)).edges ⊆ walk.edges := by
        rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
        intro pair hpair
        have hfull := SimpleGraph.mem_edgeFinset.mpr (other.edges_subset_edgeSet hpair)
        rw [R.openGraph_edgeFinset] at hfull
        obtain ⟨bond, hb, rfl⟩ := Finset.mem_image.mp hfull
        have hb := (Finset.mem_filter.mp hb).2
        by_cases heq : bond = edge
        · subst bond; simp at hb
        · rw [Function.update_of_ne heq] at hb
          exact of_decide_eq_true hb
      have heq := hpath.eq_of_edges_subset walk _ (hother.mapLe _) hsubset
      have hedge : s((R.endpoint edge).1, (R.endpoint edge).2) ∈ other.edges := by
        rw [← SimpleGraph.Walk.edges_mapLe_eq_edges (R.openGraph_le_full _) other, heq]
        exact hmem
      have hfalse := R.edge_open_of_mem_walk hsimple _ other edge hedge
      simp at hfalse
  exact ⟨configuration, by simp [pivotal, hopen, hcross, hclosed]⟩

theorem path_of_pivotal (edge : Fin edges) (configuration : Configuration edges)
    (hpivotal : R.pivotal configuration edge = true) :
    ∃ walk : R.fullGraph.Walk R.source R.target, walk.IsPath ∧
      s((R.endpoint edge).1, (R.endpoint edge).2) ∈ walk.edges := by
  have hconditions : R.crosses (Function.update configuration edge true) = true ∧
      R.crosses (Function.update configuration edge false) = false := by
    simpa [pivotal] using hpivotal
  obtain ⟨hcross, hclosed⟩ := hconditions
  obtain ⟨walk, hpath, _⟩ := ((R.crosses_eq_true _).mp hcross).exists_path_of_dist
  refine ⟨walk.mapLe (R.openGraph_le_full _), hpath.mapLe _, ?_⟩
  rw [SimpleGraph.Walk.edges_mapLe_eq_edges]
  by_contra hmissing
  have hreach := R.reachable_of_walk_edges_open (Function.update configuration edge false)
    (walk.mapLe (R.openGraph_le_full _)) (by
      intro pair hpair
      rw [SimpleGraph.Walk.edges_mapLe_eq_edges] at hpair
      have hfull := SimpleGraph.mem_edgeFinset.mpr (walk.edges_subset_edgeSet hpair)
      rw [R.openGraph_edgeFinset] at hfull
      obtain ⟨bond, hb, heq⟩ := Finset.mem_image.mp hfull
      have hne : bond ≠ edge := by rintro rfl; exact hmissing (heq.symm ▸ hpair)
      refine ⟨bond, ?_, heq⟩
      simpa only [Function.update_of_ne hne] using (Finset.mem_filter.mp hb).2)
  have := (R.crosses_eq_true _).mpr hreach
  rw [hclosed] at this
  contradiction

end
end Universality.FiniteNetwork
