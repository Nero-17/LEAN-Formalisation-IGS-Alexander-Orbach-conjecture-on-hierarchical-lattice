import Universality.Percolation.MassRowLowerBounds

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def sourceNeighbor (edge : Fin edges) : Fin vertices :=
  if (R.endpoint edge).1 = R.source then (R.endpoint edge).2 else (R.endpoint edge).1

theorem sourceNeighbor_endpoint (edge : Fin edges) (hincident : edge ∈ R.sourceIncidentEdges) :
    s((R.endpoint edge).1, (R.endpoint edge).2) = s(R.source, R.sourceNeighbor edge) := by
  have h := (Finset.mem_filter.mp hincident).2
  by_cases hfirst : (R.endpoint edge).1 = R.source
  · simp [sourceNeighbor, hfirst]
  · have hsecond := h.resolve_left hfirst
    simp only [sourceNeighbor, hfirst, ↓reduceIte, hsecond]
    exact Sym2.eq_iff.mpr (Or.inr ⟨rfl, rfl⟩)

theorem sourceNeighbor_ne_source (edge : Fin edges) (hincident : edge ∈ R.sourceIncidentEdges) :
    R.sourceNeighbor edge ≠ R.source := by
  have h := (Finset.mem_filter.mp hincident).2
  by_cases hfirst : (R.endpoint edge).1 = R.source
  · simpa only [sourceNeighbor, hfirst, ↓reduceIte] using (R.loopless edge).symm
  · simp only [sourceNeighbor, hfirst, ↓reduceIte, ne_eq, hfirst, not_false_eq_true]

theorem sourceNeighbor_image : R.sourceIncidentEdges.image R.sourceNeighbor = R.fullGraph.neighborFinset R.source := by
  ext vertex
  rw [SimpleGraph.mem_neighborFinset]
  constructor
  · rintro hmem
    obtain ⟨edge, hincident, rfl⟩ := Finset.mem_image.mp hmem
    refine ⟨(R.sourceNeighbor_ne_source edge hincident).symm, edge, rfl, ?_⟩
    have h := (Finset.mem_filter.mp hincident).2
    by_cases hfirst : (R.endpoint edge).1 = R.source
    · left
      apply Prod.ext <;> simp [sourceNeighbor, hfirst]
    · have hsecond := h.resolve_left hfirst
      right
      apply Prod.ext <;> simp [sourceNeighbor, hfirst, hsecond]
  · rintro ⟨hne, edge, _, hfirst | hsecond⟩
    · have he1 := congrArg Prod.fst hfirst
      have he2 := congrArg Prod.snd hfirst
      refine Finset.mem_image.mpr ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl he1⟩, ?_⟩
      simp [sourceNeighbor, he1, he2]
    · have he1 := congrArg Prod.fst hsecond
      have he2 := congrArg Prod.snd hsecond
      refine Finset.mem_image.mpr ⟨edge, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr he2⟩, ?_⟩
      simp [sourceNeighbor, he1, he2, hne.symm]

theorem sourceIncidentEdges_card_eq_degree
    (hsimple : Function.Injective (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2))) :
    R.sourceIncidentEdges.card = R.fullGraph.degree R.source := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← R.sourceNeighbor_image]
  symm
  apply Finset.card_image_of_injOn
  intro first hfirst second hsecond heq
  apply hsimple
  change s((R.endpoint first).1, (R.endpoint first).2) = s((R.endpoint second).1, (R.endpoint second).2)
  rw [R.sourceNeighbor_endpoint first hfirst, R.sourceNeighbor_endpoint second hsecond, heq]

end
end Universality.FiniteNetwork
