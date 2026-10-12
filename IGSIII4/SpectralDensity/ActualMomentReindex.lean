import IGSIII34.Resistance.FiniteNetwork

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section
open scoped BigOperators
variable {Vertex Edge OtherVertex OtherEdge : Type*}
  [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge] [DecidableEq Edge]
  [Fintype OtherVertex] [DecidableEq OtherVertex] [Fintype OtherEdge] [DecidableEq OtherEdge]

theorem divergence_reindex
    (network : FiniteNetwork Vertex Edge) (other : FiniteNetwork OtherVertex OtherEdge)
    (vertices : Vertex ≃ OtherVertex) (edges : Edge ≃ OtherEdge)
    (endpoint : ∀ edge, other.endpoint (edges edge) =
      (vertices (network.endpoint edge).1, vertices (network.endpoint edge).2))
    (current : Edge → ℝ) (vertex : Vertex) :
    other.divergence (fun edge => current (edges.symm edge)) (vertices vertex) =
      network.divergence current vertex := by
  unfold divergence
  rw [← edges.sum_comp]
  simp only [Equiv.symm_apply_apply, endpoint, Equiv.apply_eq_iff_eq]

theorem effectiveResistance_reindex
    (network : FiniteNetwork Vertex Edge) (other : FiniteNetwork OtherVertex OtherEdge)
    (vertices : Vertex ≃ OtherVertex) (edges : Edge ≃ OtherEdge)
    (endpoint : ∀ edge, other.endpoint (edges edge) =
      (vertices (network.endpoint edge).1, vertices (network.endpoint edge).2))
    (source : other.source = vertices network.source)
    (target : other.target = vertices network.target) (resistance : Edge → ℝ) :
    other.effectiveResistance (fun edge => resistance (edges.symm edge)) =
      network.effectiveResistance resistance := by
  have unitFlows (current : Edge → ℝ) :
      (fun edge => current (edges.symm edge)) ∈ other.unitFlows ↔ current ∈ network.unitFlows := by
    constructor
    · intro flow vertex
      have identity := flow (vertices vertex)
      rw [divergence_reindex network other vertices edges endpoint current vertex,
        source, target] at identity
      simpa only [Equiv.apply_eq_iff_eq] using identity
    · intro flow vertex
      obtain ⟨vertex, rfl⟩ := vertices.surjective vertex
      rw [divergence_reindex network other vertices edges endpoint current vertex, source, target]
      simpa only [Equiv.apply_eq_iff_eq] using flow vertex
  have energies (current : Edge → ℝ) :
      energy (fun edge => resistance (edges.symm edge)) (fun edge => current (edges.symm edge)) =
        energy resistance current := by
    unfold energy
    rw [← edges.sum_comp]
    simp only [Equiv.symm_apply_apply]
  unfold effectiveResistance
  congr 1
  ext value
  constructor
  · rintro ⟨current, flow, identity⟩
    let pulled : Edge → ℝ := fun edge => current (edges edge)
    have transport : (fun edge => pulled (edges.symm edge)) = current := by
      funext edge
      simp only [pulled, Equiv.apply_symm_apply]
    refine ⟨pulled, (unitFlows pulled).mp (transport.symm ▸ flow), ?_⟩
    rw [← energies pulled, transport]
    exact identity
  · rintro ⟨current, flow, identity⟩
    exact ⟨_, (unitFlows current).mpr flow, (energies current).trans identity⟩

end
end IGSIII34.Resistance.FiniteNetwork
