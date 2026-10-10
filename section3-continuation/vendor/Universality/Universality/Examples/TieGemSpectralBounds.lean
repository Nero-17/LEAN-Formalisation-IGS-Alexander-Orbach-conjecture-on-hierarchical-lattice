import Universality.Examples.GemMassBlockBounds
import Universality.Matrix.PositiveRootTestRatio
import Universality.Matrix.RealDiagonalization

namespace Universality
noncomputable section
open Matrix FiniteNetwork
set_option backward.isDefEq.respectTransparency false

/-- The interval encloses the actual complex spectral radius, and therefore
certifies the displayed four-place value 5.7087. -/
theorem gem_critical_spectralRadius_fine_bounds (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    (5708705 : ℝ) / 1000000 <
      (spectralRadius ℂ ((gemRule.network.massMatrix p).map Complex.ofReal)).toReal ∧
    (spectralRadius ℂ ((gemRule.network.massMatrix p).map Complex.ofReal)).toReal <
      (5708725 : ℝ) / 1000000 := by
  rw [gem_mass_spectralRadius_eq_positiveRoot p hp hp']
  obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd⟩ :=
    gemMassBlockFormula_rational_bounds p hp hp' hfixed
  constructor
  · apply lt_positiveRoot_of_test_ratio _ (gemMassBlockFormula_pos p hp hp')
      ((459389 : ℝ) / 1000000) _ (by norm_num)
    · linarith
    · rw [hd]
      linarith
  · apply positiveRoot_lt_of_test_ratio _ (gemMassBlockFormula_pos p hp hp')
      ((459389 : ℝ) / 1000000) _ (by norm_num)
    · linarith
    · rw [hd]
      linarith

theorem gem_critical_spectralRadius_rational_bounds (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    (570865 : ℝ) / 100000 <
      (spectralRadius ℂ ((gemRule.network.massMatrix p).map Complex.ofReal)).toReal ∧
    (spectralRadius ℂ ((gemRule.network.massMatrix p).map Complex.ofReal)).toReal <
      (570875 : ℝ) / 100000 := by
  obtain ⟨hl, hu⟩ := gem_critical_spectralRadius_fine_bounds p hp hp' hfixed
  constructor <;> linarith

/-- Cyclic substitution transfers the certified value to the actual tie model. -/
theorem tie_critical_spectralRadius_bounds_of_gem (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    (570865 : ℝ) / 100000 <
      (spectralRadius ℂ ((tieRule.network.massMatrix (p ^ 2)).map Complex.ofReal)).toReal ∧
    (spectralRadius ℂ ((tieRule.network.massMatrix (p ^ 2)).map Complex.ofReal)).toReal <
      (570875 : ℝ) / 100000 := by
  rw [← tie_gem_spectralRadius p hp hp' hfixed]
  exact gem_critical_spectralRadius_rational_bounds p hp hp' hfixed

/-- The second root of the invariant positive block is an eigenvalue of the
full three-state matrix; its lifted eigenvector is nonzero. -/
theorem massPlane_secondaryRoot_mem_spectrum
    (M : Matrix LiveState LiveState ℝ) (hplane : PreservesMassPlane M)
    (hblock : ∀ i j, 0 < massPlaneBlock M i j) :
    (secondaryRoot (massPlaneBlock M) : ℂ) ∈ spectrum ℂ (M.map Complex.ofReal) := by
  have hquad := secondaryRoot_quadratic (massPlaneBlock M) hblock
  rw [Matrix.trace_fin_two, Matrix.det_fin_two] at hquad
  have hvec : massPlaneBlock M *ᵥ
      ![massPlaneBlock M 0 1, secondaryRoot (massPlaneBlock M) - massPlaneBlock M 0 0] =
      secondaryRoot (massPlaneBlock M) •
      ![massPlaneBlock M 0 1, secondaryRoot (massPlaneBlock M) - massPlaneBlock M 0 0] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> nlinarith
  have hlift : M *ᵥ massPlaneLift
      ![massPlaneBlock M 0 1, secondaryRoot (massPlaneBlock M) - massPlaneBlock M 0 0] =
      secondaryRoot (massPlaneBlock M) • massPlaneLift
      ![massPlaneBlock M 0 1, secondaryRoot (massPlaneBlock M) - massPlaneBlock M 0 0] := by
    rw [hplane, hvec, massPlaneLift_smul]
  rw [← Matrix.spectrum_toLin', ← Module.End.hasEigenvalue_iff_mem_spectrum]
  apply Module.End.hasEigenvalue_of_hasEigenvector
    (x := fun state => ((massPlaneLift
      ![massPlaneBlock M 0 1, secondaryRoot (massPlaneBlock M) - massPlaneBlock M 0 0]
      state : ℝ) : ℂ))
  constructor
  · rw [Module.End.mem_eigenspace_iff]
    ext state
    change (∑ j, (M state j : ℂ) * ((massPlaneLift
      ![massPlaneBlock M 0 1, secondaryRoot (massPlaneBlock M) - massPlaneBlock M 0 0] j : ℝ) : ℂ)) =
      (secondaryRoot (massPlaneBlock M) : ℂ) * ((massPlaneLift
      ![massPlaneBlock M 0 1, secondaryRoot (massPlaneBlock M) - massPlaneBlock M 0 0] state : ℝ) : ℂ)
    have hv := congrFun hlift state
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at hv
    exact_mod_cast hv
  · intro hz
    have hv := congrFun hz .connected
    change (massPlaneBlock M 0 1 : ℂ) = 0 at hv
    exact (hblock 0 1).ne' (by exact_mod_cast hv)

theorem gem_secondaryRoot_mem_spectrum (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    (secondaryRoot (gemMassBlockFormula p) : ℂ) ∈
      spectrum ℂ ((gemRule.network.massMatrix p).map Complex.ofReal) := by
  rw [← gem_massPlaneBlock p hp hp']
  obtain ⟨symmetry, hs, ht⟩ := gemRule_classical.massAdmissible.symmetric
  exact massPlane_secondaryRoot_mem_spectrum _
    (gemRule.network.massMatrix_preservesMassPlane p symmetry hs ht)
    (by rw [gem_massPlaneBlock p hp hp']; exact gemMassBlockFormula_pos p hp hp')

theorem gem_critical_secondaryRoot_rational_bounds (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : gemRule.network.reliability p = p) :
    (142005 : ℝ) / 100000 < secondaryRoot (gemMassBlockFormula p) ∧
      secondaryRoot (gemMassBlockFormula p) < (142015 : ℝ) / 100000 := by
  obtain ⟨hl, hu⟩ := gem_critical_spectralRadius_fine_bounds p hp hp' hfixed
  rw [gem_mass_spectralRadius_eq_positiveRoot p hp hp'] at hl hu
  obtain ⟨ha0, ha1, hb0, hb1, hc0, hc1, hd⟩ :=
    gemMassBlockFormula_rational_bounds p hp hp' hfixed
  rw [secondaryRoot, Matrix.trace_fin_two, hd]
  constructor <;> linarith

end
end Universality
