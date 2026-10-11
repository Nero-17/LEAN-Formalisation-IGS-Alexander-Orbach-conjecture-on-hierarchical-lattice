import Universality.Graph.IncidentDegree
import Universality.Percolation.CountingPolynomials

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem openGraph_edgeFinset (configuration : Configuration edges) :
    (R.openGraph configuration).edgeFinset =
      (Finset.univ.filter fun edge => configuration edge = true).image
        (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2)) := by
  ext pair
  refine Sym2.inductionOn pair (fun first second => ?_)
  simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
  constructor
  · rintro ⟨hne, edge, hopen, hfirst | hsecond⟩
    · exact Finset.mem_image.mpr ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hopen⟩,
        by simp only [hfirst]⟩
    · exact Finset.mem_image.mpr ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hopen⟩,
        by simp only [hsecond]; exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro hmem
    obtain ⟨edge, hopened, heq⟩ := Finset.mem_image.mp hmem
    have hopen := (Finset.mem_filter.mp hopened).2
    rcases Sym2.eq_iff.mp heq with ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
    · refine ⟨?_, edge, hopen, Or.inl (Prod.ext hfirst hsecond)⟩
      simpa only [hfirst, hsecond] using R.loopless edge
    · refine ⟨?_, edge, hopen, Or.inr (Prod.ext hfirst hsecond)⟩
      simpa only [hfirst, hsecond] using (R.loopless edge).symm

theorem distance_le_openCount (configuration : Configuration edges) (hcross : R.crosses configuration = true) :
    R.fullGraph.dist R.source R.target ≤ openCount configuration := by
  have hreach := (R.crosses_eq_true configuration).mp hcross
  have hle : R.openGraph configuration ≤ R.fullGraph := by
    intro first second hadj
    obtain ⟨hne, edge, _, hendpoint⟩ := hadj
    exact ⟨hne, edge, rfl, hendpoint⟩
  obtain ⟨walk, hpath, hlength⟩ := hreach.exists_path_of_dist
  calc
    _ ≤ (R.openGraph configuration).dist R.source R.target := hreach.dist_anti hle
    _ = walk.length := hlength.symm
    _ ≤ (R.openGraph configuration).edgeFinset.card := hpath.isTrail.length_le_card_edgeFinset
    _ ≤ openCount configuration := by
      rw [R.openGraph_edgeFinset]
      exact Finset.card_image_le

theorem reachable_of_walk_edges_open {source target : Fin vertices}
    (configuration : Configuration edges) (walk : R.fullGraph.Walk source target)
    (hopen : ∀ pair ∈ walk.edges, ∃ edge, configuration edge = true ∧
      s((R.endpoint edge).1, (R.endpoint edge).2) = pair) :
    (R.openGraph configuration).Reachable source target := by
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons first second last hadj tail ih =>
    have hfirst := hopen s(first, second) (by simp)
    obtain ⟨edge, hopenEdge, heq⟩ := hfirst
    have hadjOpen : (R.openGraph configuration).Adj first second := by
      refine ⟨hadj.ne, edge, hopenEdge, ?_⟩
      rcases Sym2.eq_iff.mp heq with ⟨he1, he2⟩ | ⟨he1, he2⟩
      · exact Or.inl (Prod.ext he1 he2)
      · exact Or.inr (Prod.ext he1 he2)
    exact hadjOpen.reachable.trans (ih (fun pair hpair => hopen pair (by simp [hpair])))

theorem exists_crossing_configuration_minimum_size
    (hsimple : Function.Injective (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2)))
    (hconnected : R.fullGraph.Reachable R.source R.target) :
    ∃ configuration, R.crosses configuration = true ∧
      openCount configuration = R.fullGraph.dist R.source R.target := by
  classical
  obtain ⟨walk, hpath, hlength⟩ := hconnected.exists_path_of_dist
  let configuration : Configuration edges := fun edge =>
    decide (s((R.endpoint edge).1, (R.endpoint edge).2) ∈ walk.edges)
  have hexists (pair : Sym2 (Fin vertices)) (hpair : pair ∈ walk.edges) :
      ∃ edge, configuration edge = true ∧ s((R.endpoint edge).1, (R.endpoint edge).2) = pair := by
    have hmem : pair ∈ R.fullGraph.edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr (walk.edges_subset_edgeSet hpair)
    change pair ∈ (R.openGraph (fun _ => true)).edgeFinset at hmem
    rw [R.openGraph_edgeFinset] at hmem
    obtain ⟨edge, _, heq⟩ := Finset.mem_image.mp hmem
    exact ⟨edge, by simp [configuration, heq, hpair], heq⟩
  refine ⟨configuration, (R.crosses_eq_true _).mpr (R.reachable_of_walk_edges_open configuration walk hexists), ?_⟩
  have himage : (Finset.univ.filter fun edge => configuration edge = true).image
      (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2)) = walk.edges.toFinset := by
    ext pair
    constructor
    · intro hmem
      obtain ⟨edge, hopen, rfl⟩ := Finset.mem_image.mp hmem
      simpa [configuration] using (Finset.mem_filter.mp hopen).2
    · intro hmem
      obtain ⟨edge, hopen, heq⟩ := hexists pair (List.mem_toFinset.mp hmem)
      exact Finset.mem_image.mpr ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hopen⟩, heq⟩
  have hcard := congrArg Finset.card himage
  rw [Finset.card_image_of_injective _ hsimple, List.toFinset_card_of_nodup hpath.isTrail.edges_nodup,
    SimpleGraph.Walk.length_edges, hlength] at hcard
  exact hcard

end
end Universality.FiniteNetwork
