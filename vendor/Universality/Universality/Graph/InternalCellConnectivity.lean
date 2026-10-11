import Universality.Graph.SubstitutionNetwork

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem cellVertex_eq_interior (edge : Fin outerEdges) (vertex : S.InteriorVertex) :
    R.cellVertex S edge vertex.val = Sum.inr (edge, vertex) := by
  simp only [cellVertex, dif_neg vertex.property.1, dif_neg vertex.property.2]
  rfl

theorem cellVertex_eq_interior_iff (edge other : Fin outerEdges)
    (vertex : Fin innerVertices) (inside : S.InteriorVertex) :
    R.cellVertex S edge vertex = Sum.inr (other, inside) ↔ edge = other ∧ vertex = inside.val := by
  by_cases hs : vertex = S.source
  · subst vertex
    simp [R.cellVertex_source, Ne.symm inside.property.1]
  · by_cases ht : vertex = S.target
    · subst vertex
      simp [R.cellVertex_target, Ne.symm inside.property.2]
    · simp only [cellVertex, dif_neg hs, dif_neg ht]
      constructor
      · intro heq
        have hpair := Sum.inr.inj heq
        exact ⟨congrArg Prod.fst hpair, congrArg (fun pair : Fin outerEdges × S.InteriorVertex => pair.2.val) hpair⟩
      · rintro ⟨rfl, heq⟩
        subst vertex
        rfl

/-- A child component avoiding its two terminals cannot escape into another
cell after gluing. This is the pathwise fact used in the birth decomposition. -/
theorem internal_cell_reachable_iff (configuration : Fin outerEdges → Configuration innerEdges)
    (edge : Fin outerEdges) (root : Fin innerVertices)
    (hsource : ¬ (S.openGraph (configuration edge)).Reachable root S.source)
    (htarget : ¬ (S.openGraph (configuration edge)).Reachable root S.target)
    (vertex : R.SubstitutionVertex S) :
    (R.substitutedGraph S configuration).Reachable (R.cellVertex S edge root) vertex ↔
      ∃ inside : Fin innerVertices, (S.openGraph (configuration edge)).Reachable root inside ∧
        R.cellVertex S edge inside = vertex := by
  constructor
  · intro hreachable
    have hstep {first second : R.SubstitutionVertex S}
        (hadj : (R.substitutedGraph S configuration).Adj first second)
        (hfirst : ∃ inside : Fin innerVertices,
          (S.openGraph (configuration edge)).Reachable root inside ∧ R.cellVertex S edge inside = first) :
        ∃ inside : Fin innerVertices,
          (S.openGraph (configuration edge)).Reachable root inside ∧ R.cellVertex S edge inside = second := by
      obtain ⟨inside, hreach, rfl⟩ := hfirst
      have hs : inside ≠ S.source := fun heq => hsource (heq ▸ hreach)
      have ht : inside ≠ S.target := fun heq => htarget (heq ▸ hreach)
      obtain ⟨_, other, start, finish, hlocal, hstart, hfinish⟩ := hadj
      have heq : R.cellVertex S other start = Sum.inr (edge, ⟨inside, hs, ht⟩) := by
        rw [hstart]
        exact R.cellVertex_eq_interior S edge ⟨inside, hs, ht⟩
      obtain ⟨rfl, rfl⟩ := (R.cellVertex_eq_interior_iff S other edge start ⟨inside, hs, ht⟩).mp heq
      exact ⟨finish, hreach.trans hlocal.reachable, hfinish⟩
    obtain ⟨walk⟩ := hreachable
    have hpropagate {first second : R.SubstitutionVertex S}
        (walk : (R.substitutedGraph S configuration).Walk first second) :
        (∃ inside : Fin innerVertices, (S.openGraph (configuration edge)).Reachable root inside ∧
          R.cellVertex S edge inside = first) →
        ∃ inside : Fin innerVertices, (S.openGraph (configuration edge)).Reachable root inside ∧
          R.cellVertex S edge inside = second := by
      induction walk with
      | nil => exact id
      | cons hadj tail ih => exact fun h => ih (hstep hadj h)
    exact hpropagate walk ⟨root, .refl root, rfl⟩
  · rintro ⟨inside, hreach, rfl⟩
    exact hreach.map (R.cellHom S configuration edge)

end
end Universality.FiniteNetwork
