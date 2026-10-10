import IGSIII34.Resistance.Dirichlet

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge OtherVertex OtherEdge : Type*}
  [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
  [Fintype OtherVertex] [DecidableEq OtherVertex] [Fintype OtherEdge] [DecidableEq OtherEdge]

theorem potentialEnergy_reindex
    (network : FiniteNetwork Vertex Edge) (other : FiniteNetwork OtherVertex OtherEdge)
    (vertices : Vertex ≃ OtherVertex) (edges : Edge ≃ OtherEdge)
    (endpoint : ∀ edge, other.endpoint (edges edge) =
      (vertices (network.endpoint edge).1, vertices (network.endpoint edge).2))
    (resistance : Edge → ℝ) (potential : OtherVertex → ℝ) :
    other.potentialEnergy (fun edge => resistance (edges.symm edge)) potential =
      network.potentialEnergy resistance (fun vertex => potential (vertices vertex)) := by
  unfold potentialEnergy
  rw [← edges.sum_comp]
  simp only [Equiv.symm_apply_apply, endpoint]

theorem effectiveConductance_reindex
    (network : FiniteNetwork Vertex Edge) (other : FiniteNetwork OtherVertex OtherEdge)
    (vertices : Vertex ≃ OtherVertex) (edges : Edge ≃ OtherEdge)
    (endpoint : ∀ edge, other.endpoint (edges edge) =
      (vertices (network.endpoint edge).1, vertices (network.endpoint edge).2))
    (source : other.source = vertices network.source)
    (target : other.target = vertices network.target) (resistance : Edge → ℝ) :
    other.effectiveConductance (fun edge => resistance (edges.symm edge)) =
      network.effectiveConductance resistance := by
  unfold effectiveConductance
  congr 1
  ext value
  constructor
  · rintro ⟨potential, atSource, atTarget, energy⟩
    refine ⟨fun vertex => potential (vertices vertex), ?_, ?_, ?_⟩
    · simpa only [source] using atSource
    · simpa only [target] using atTarget
    · rw [← potentialEnergy_reindex network other vertices edges endpoint]
      exact energy
  · rintro ⟨potential, atSource, atTarget, energy⟩
    refine ⟨fun vertex => potential (vertices.symm vertex), ?_, ?_, ?_⟩
    · simpa only [source, Equiv.symm_apply_apply] using atSource
    · simpa only [target, Equiv.symm_apply_apply] using atTarget
    · rw [potentialEnergy_reindex network other vertices edges endpoint]
      simpa only [Equiv.symm_apply_apply] using energy

end
end IGSIII34.Resistance.FiniteNetwork
