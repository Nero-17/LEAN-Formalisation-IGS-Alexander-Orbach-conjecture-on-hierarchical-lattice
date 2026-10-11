import Universality.Percolation.ClosedCoarseRadius
import Universality.Examples.DiamondRadiusGeometry

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

theorem allClosed_terminal_distance_bound
    (hinner : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (diameter : ℕ) (cells : Fin outerEdges → Configuration innerEdges)
    (hterminalBound : ∀ edge vertex,
      ((S.openGraph (cells edge)).Reachable S.source vertex → S.fullGraph.dist S.source vertex ≤ diameter) ∧
      ((S.openGraph (cells edge)).Reachable S.target vertex → S.fullGraph.dist S.target vertex ≤ diameter))
    (hcoarse : S.coarseConfiguration cells = fun _ => false)
    (vertex : Fin (Fintype.card (R.SubstitutionVertex S))) :
    (((R.substitute S).openGraph (substitutionConfigurationEquiv cells)).Reachable
        (R.substitute S).source vertex → (R.substitute S).fullGraph.dist (R.substitute S).source vertex ≤ diameter) ∧
    (((R.substitute S).openGraph (substitutionConfigurationEquiv cells)).Reachable
        (R.substitute S).target vertex → (R.substitute S).fullGraph.dist (R.substitute S).target vertex ≤ diameter) := by
  exact ⟨fun hreach => R.allClosed_coarseRoot_distance_le_terminal_bound S hinner diameter cells
      hterminalBound hcoarse R.source vertex hreach,
    fun hreach => R.allClosed_coarseRoot_distance_le_terminal_bound S hinner diameter cells
      hterminalBound hcoarse R.target vertex hreach⟩

end
end Universality.FiniteNetwork

namespace Universality
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {vertices edges : ℕ} (S : FiniteNetwork vertices edges)

/-- Two failed coarse generations still have terminal attachment radius at
most one deepest-cell diameter. -/
theorem diamond_double_closed_terminal_bound
    (hconnected : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (diameter : ℕ) (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ diameter)
    (cells : Fin 4 → Fin 4 → Configuration edges)
    (hclosed : ∀ first second, S.crosses (cells first second) = false)
    (vertex : Fin (Fintype.card (diamondNetwork.SubstitutionVertex (diamondNetwork.substitute S)))) :
    let main := diamondNetwork.substitute (diamondNetwork.substitute S)
    let configuration := substitutionConfigurationEquiv (fun edge => substitutionConfigurationEquiv (cells edge))
    ((main.openGraph configuration).Reachable main.source vertex → main.fullGraph.dist main.source vertex ≤ diameter) ∧
      ((main.openGraph configuration).Reachable main.target vertex → main.fullGraph.dist main.target vertex ≤ diameter) := by
  have hcoarse (edge : Fin 4) : S.coarseConfiguration (cells edge) = fun _ => false :=
    funext (hclosed edge)
  have hinnerClosed (edge : Fin 4) :
      (diamondNetwork.substitute S).crosses (substitutionConfigurationEquiv (cells edge)) = false := by
    rw [diamondNetwork.substitute_crosses S, hcoarse, diamondNetwork.crosses_all_closed]
  exact diamondNetwork.allClosed_terminal_distance_bound (diamondNetwork.substitute S)
    (diamondNetwork.substitute_all_vertices_connected S diamondRule_classical.connected hconnected)
    diameter (fun edge => substitutionConfigurationEquiv (cells edge))
    (fun edge point => diamondNetwork.allClosed_terminal_distance_bound S hconnected diameter
      (cells edge) (fun _ point => ⟨fun _ => hdiameter _ point, fun _ => hdiameter _ point⟩)
      (hcoarse edge) point)
    (funext hinnerClosed) vertex

end
end Universality

