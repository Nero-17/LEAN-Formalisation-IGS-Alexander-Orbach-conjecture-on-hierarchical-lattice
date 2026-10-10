import Universality.Examples.TieGemSpectralBounds
namespace Universality
noncomputable section
open Matrix FiniteNetwork
set_option backward.isDefEq.respectTransparency false

theorem tie_gem_nonzero_spectrum (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) (value : ℂ) (hne : value ≠ 0) :
    value ∈ spectrum ℂ ((gemRule.network.massMatrix p).map Complex.ofReal) ↔
      value ∈ spectrum ℂ ((tieRule.network.massMatrix (p ^ 2)).map Complex.ofReal) := by
  have hprob : 0 < twoEdgePathNetwork.reliability p := by rw [twoEdgePath_reliability]; positivity
  have hprob' : twoEdgePathNetwork.reliability p < 1 := twoEdgePathNetwork.reliability_lt_one hp hp'
  have hfixed' : triangleNetwork.reliability (p ^ 2) = p := by
    simpa only [gemRule, Rule.mul_reliability, triangleRule, twoEdgePathRule,
      twoEdgePath_reliability] using hfixed
  have hgem := Rule.mul_massMatrix triangleRule twoEdgePathRule p hprob hprob'
    twoEdgePathTerminalSymmetry (by decide) (by decide)
  have htie := Rule.mul_massMatrix twoEdgePathRule triangleRule (p ^ 2)
    (by change 0 < triangleNetwork.reliability (p ^ 2); rwa [hfixed'])
    (by change triangleNetwork.reliability (p ^ 2) < 1; rwa [hfixed'])
    triangleTerminalSymmetry (by decide) (by decide)
  change tieRule.network.massMatrix (p ^ 2) =
    twoEdgePathNetwork.massMatrix (triangleNetwork.reliability (p ^ 2)) *
      triangleNetwork.massMatrix (p ^ 2) at htie
  rw [hfixed'] at htie
  change gemRule.network.massMatrix p = triangleNetwork.massMatrix
    (twoEdgePathNetwork.reliability p) * twoEdgePathNetwork.massMatrix p at hgem
  rw [twoEdgePath_reliability] at hgem
  rw [hgem, htie]
  change value ∈ spectrum ℂ (Complex.ofRealHom.mapMatrix
    (triangleNetwork.massMatrix (p ^ 2) * twoEdgePathNetwork.massMatrix p)) ↔
    value ∈ spectrum ℂ (Complex.ofRealHom.mapMatrix
    (twoEdgePathNetwork.massMatrix p * triangleNetwork.massMatrix (p ^ 2)))
  rw [map_mul, map_mul]
  exact spectrum.unit_mem_mul_comm (r := Units.mk0 value hne)

/-- The smaller positive-block eigenvalue belongs to both actual full spectra,
with a rational enclosure certifying the common four-place value 1.4201. -/
theorem tie_gem_critical_secondary_eigenvalue (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    (secondaryRoot (gemMassBlockFormula p) : ℂ) ∈
        spectrum ℂ ((gemRule.network.massMatrix p).map Complex.ofReal) ∧
    (secondaryRoot (gemMassBlockFormula p) : ℂ) ∈
        spectrum ℂ ((tieRule.network.massMatrix (p ^ 2)).map Complex.ofReal) ∧
    (142005 : ℝ) / 100000 < secondaryRoot (gemMassBlockFormula p) ∧
      secondaryRoot (gemMassBlockFormula p) < (142015 : ℝ) / 100000 := by
  have hbounds := gem_critical_secondaryRoot_rational_bounds p hp hp' hfixed
  have hmem := gem_secondaryRoot_mem_spectrum p hp hp'
  refine ⟨hmem, ?_, hbounds⟩
  apply (tie_gem_nonzero_spectrum p hp hp' hfixed _ ?_).mp hmem
  have hpos : 0 < secondaryRoot (gemMassBlockFormula p) := by linarith [hbounds.1]
  exact_mod_cast hpos.ne'

end
end Universality
