import Universality.Examples.TriangleMassFormula
import Universality.Percolation.MassSpectralLowerBound
import Universality.Examples.TieGemClassical

namespace Universality
noncomputable section
open Matrix FiniteNetwork
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def gemMassBlockFormula (p : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * ((1 + 4 * p ^ 2 - 2 * (p ^ 2) ^ 2) / (1 + p ^ 2 - (p ^ 2) ^ 2)) +
      ((2 + 2 * p ^ 2 - 4 * (p ^ 2) ^ 2) / (1 + p ^ 2 - (p ^ 2) ^ 2)) * p / (1 + p),
    (2 + 2 * p ^ 2 - 4 * (p ^ 2) ^ 2) / (1 + p ^ 2 - (p ^ 2) ^ 2);
    2 * p ^ 2 / (1 + p ^ 2) + 2 * p / (1 + p), 2]

/-- This block is the restriction of the actual gem live-edge mass operator. -/
theorem gem_massPlaneBlock (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    massPlaneBlock (gemRule.network.massMatrix p) = gemMassBlockFormula p := by
  have hp2 : 0 < p ^ 2 := pow_pos hp 2
  have hp2' : p ^ 2 < 1 := by nlinarith
  have hgem := Rule.mul_massMatrix triangleRule twoEdgePathRule p
    (by change 0 < twoEdgePathNetwork.reliability p; rw [twoEdgePath_reliability]; exact hp2)
    (by change twoEdgePathNetwork.reliability p < 1; rw [twoEdgePath_reliability]; exact hp2')
    twoEdgePathTerminalSymmetry (by decide) (by decide)
  change gemRule.network.massMatrix p = triangleNetwork.massMatrix
    (twoEdgePathNetwork.reliability p) * twoEdgePathNetwork.massMatrix p at hgem
  rw [twoEdgePath_reliability, triangle_massMatrix _ hp2 hp2', twoEdgePath_massMatrix p hp hp'] at hgem
  rw [hgem]
  have hplus : 1 + p ≠ 0 := by linarith
  have hplus2 : 1 + p ^ 2 ≠ 0 := by positivity
  have hquad : 1 + p ^ 2 - (p ^ 2) ^ 2 ≠ 0 := by
    nlinarith [mul_pos hp2 (sub_pos.mpr hp2')]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massPlaneBlock, gemMassBlockFormula, Matrix.mul_apply, sum_liveState,
      triangleMassFormula, twoEdgePathMassFormula] <;>
    field_simp [hplus, hplus2, hquad] <;> ring

theorem gem_mass_spectralRadius_eq_positiveRoot (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    (spectralRadius ℂ ((gemRule.network.massMatrix p).map Complex.ofReal)).toReal =
      positiveRoot (gemMassBlockFormula p) := by
  obtain ⟨symmetry, hs, ht⟩ := gemRule_classical.massAdmissible.symmetric
  have hblock := (gemRule.network.massPlaneBlock_pos_of_geometry hp hp'
    (gemRule_classical.connected _) gemRule_classical.scale gemRule_classical.cut).1
  rw [massPlane_spectralRadius _ (gemRule.network.massMatrix_nonneg hp.le hp'.le)
    (gemRule.network.massMatrix_preservesMassPlane p symmetry hs ht) hblock,
    ENNReal.toReal_ofReal (positiveRoot_pos _ hblock).le, gem_massPlaneBlock p hp hp']

theorem gemMassBlockFormula_pos (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    ∀ i j, 0 < gemMassBlockFormula p i j := by
  rw [← gem_massPlaneBlock p hp hp']
  exact (gemRule.network.massPlaneBlock_pos_of_geometry hp hp'
    (gemRule_classical.connected _) gemRule_classical.scale gemRule_classical.cut).1

end
end Universality
