import IGSIII34.Spectral.Collars.FivefoldDiamondResistance
import IGSIII34.AO.MassGrowthEdgeBound
import IGSIII34.AO.SubdividedDiamondBound

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation

/-- The worked non-AO example uses the actual critical mass matrix and
actual natural electrical witness of the fivefold subdivided diamond. -/
theorem fivefoldDiamond_actual_spectral_dimension_bound
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : fivefoldDiamondRule.network.reliability p = p)
    (natural : NaturalResistanceCompletion fivefoldDiamondRule p positive belowOne fixedPoint) :
    typicalSpectralDimension
        (spectralRadius ℂ ((fivefoldDiamondRule.network.massMatrix p).map Complex.ofReal)).toReal
        natural.growth ≤ Real.log 20 / Real.log 10 ∧
      typicalSpectralDimension
        (spectralRadius ℂ ((fivefoldDiamondRule.network.massMatrix p).map Complex.ofReal)).toReal
        natural.growth < (4 / 3 : ℝ) := by
  apply spectral_bound_of_twenty_edges_five_resistance
  · exact (fivefoldDiamondRule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint
      fivefoldDiamondRule_classical.scale).trans
      (fivefoldDiamondRule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        fivefoldDiamondRule_classical.massAdmissible.symmetric fivefoldDiamondRule_classical.scale).2.1
  · exact IGSIII34.AO.classical_mass_spectralRadius_le_edges
      fivefoldDiamondRule fivefoldDiamondRule_classical p positive belowOne
  · exact fivefoldDiamond_natural_resistance_growth_lower p positive belowOne fixedPoint natural

/-- Actual critical parameters and a natural electrical law exist for the
explicit strict non-AO example; no growth or critical-point existence is assumed. -/
theorem exists_fivefoldDiamond_strict_non_AO :
    ∃ p : ℝ, ∃ positive : 0 < p, ∃ belowOne : p < 1,
      ∃ fixedPoint : fivefoldDiamondRule.network.reliability p = p,
      ∃ natural : NaturalResistanceCompletion fivefoldDiamondRule p positive belowOne fixedPoint,
        typicalSpectralDimension
          (spectralRadius ℂ ((fivefoldDiamondRule.network.massMatrix p).map Complex.ofReal)).toReal
          natural.growth < (4 / 3 : ℝ) := by
  obtain ⟨p, positive, belowOne, fixedPoint⟩ := fivefoldDiamond_critical_exists
  obtain ⟨natural⟩ := exists_natural_resistance_completion fivefoldDiamondRule
    fivefoldDiamondRule_classical p positive belowOne fixedPoint
  exact ⟨p, positive, belowOne, fixedPoint, natural,
    (fivefoldDiamond_actual_spectral_dimension_bound p positive belowOne fixedPoint natural).2⟩

end
end IGSIII34.Spectral
