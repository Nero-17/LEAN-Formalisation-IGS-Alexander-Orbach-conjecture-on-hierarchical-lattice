import IGSIII.Geometry.CellLocalisationInnerRadius
import Universality.Graph.NetworkEquivalence

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution

variable {First Second : Type*} [Fintype First] [DecidableEq First]
    [Fintype Second] [DecidableEq Second]

theorem weightedDistance_map_le {firstGraph : SimpleGraph First} {secondGraph : SimpleGraph Second}
    (hom : firstGraph →g secondGraph) (cost : Sym2 Second → ℝ)
    (nonnegative : ∀ bond, 0 ≤ cost bond)
    {first last : First} (reachable : firstGraph.Reachable first last) :
    weightedDistance secondGraph cost (hom first) (hom last) ≤
      weightedDistance firstGraph (fun bond => cost (bond.map hom)) first last := by
  obtain ⟨walk, _, minimum⟩ := exists_weighted_geodesic firstGraph
    (fun bond => cost (bond.map hom)) reachable
  have bound := weightedDistance_le_walkCost secondGraph cost nonnegative (walk.map hom)
  rw [SimpleGraph.Walk.edges_map, List.map_map] at bound
  exact bound.trans_eq minimum

theorem weightedDistance_graphIso {firstGraph : SimpleGraph First} {secondGraph : SimpleGraph Second}
    (iso : firstGraph ≃g secondGraph) (cost : Sym2 Second → ℝ)
    (nonnegative : ∀ bond, 0 ≤ cost bond) (first last : First) :
    weightedDistance secondGraph cost (iso first) (iso last) =
      weightedDistance firstGraph (fun bond => cost (bond.map iso)) first last := by
  classical
  by_cases reachable : firstGraph.Reachable first last
  · apply le_antisymm (weightedDistance_map_le iso.toHom cost nonnegative reachable)
    have bound := weightedDistance_map_le iso.symm.toHom
      (fun bond => cost (bond.map iso)) (fun bond => nonnegative _) (reachable.map iso.toHom)
    change weightedDistance firstGraph (fun bond => cost (bond.map iso))
      (iso.symm (iso first)) (iso.symm (iso last)) ≤
        weightedDistance secondGraph (fun bond => cost ((bond.map iso.symm).map iso))
          (iso first) (iso last) at bound
    simpa only [SimpleGraph.Iso.toHom, RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding, RelIso.symm_apply_apply, Sym2.map_map, Function.comp_def,
      RelIso.apply_symm_apply, Sym2.map_id', id_eq] using bound
  · have disconnected : ¬ secondGraph.Reachable (iso first) (iso last) := fun reached =>
      reachable (iso.reachable_iff.mp reached)
    simp only [weightedDistance, dif_neg reachable, dif_neg disconnected]

end
end IGSIII.Geometry



