import IGSIII34.Spectral.Collars.FivefoldDiamondGraph
import Universality.Examples.DiamondClassical
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork Matrix

def fivefoldDiamondPlantedVertex : Fin 4 ↪ Fin 20 :=
  ⟨![0,1,6,15], by decide⟩

def fivefoldDiamondSubdivisionPath : Fin 4 → Fin 6 → Fin 20 :=
  ![![0,2,3,4,5,6], ![6,7,8,9,10,1], ![0,11,12,13,14,15], ![15,16,17,18,19,1]]

def fivefoldDiamondSubedge : Fin 4 × Fin 5 ≃ Fin 20 := finProdFinEquiv

/-- Each original diamond edge is replaced by exactly five actual edges,
with its original planted endpoint images preserved. -/
theorem fivefoldDiamond_actual_subdivision :
    (∀ edge : Fin 4,
      fivefoldDiamondSubdivisionPath edge 0 = fivefoldDiamondPlantedVertex (diamondNetwork.endpoint edge).1 ∧
      fivefoldDiamondSubdivisionPath edge 5 = fivefoldDiamondPlantedVertex (diamondNetwork.endpoint edge).2) ∧
    (∀ edge : Fin 4, ∀ index : Fin 5,
      fivefoldDiamondNetwork.endpoint (fivefoldDiamondSubedge (edge,index)) =
        (fivefoldDiamondSubdivisionPath edge index.castSucc, fivefoldDiamondSubdivisionPath edge index.succ)) := by
  decide

end
end IGSIII34.Spectral
