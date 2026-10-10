import Universality.Percolation.FiniteMassDimension
import Universality.Matrix.PivotalRightVector
import Universality.Matrix.TwoByTwoExpansion

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem reliability_derivative_nonneg {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    0 ≤ deriv R.reliability p := by
  rw [R.russo_formula]
  unfold expectation
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (bernoulliWeight_nonneg hp hp' ω) (Nat.cast_nonneg _)

/-- The disconnected row gives a direct strict upper bound for the response
eigenvalue. No abstract simplicity theorem for primitive matrices is needed. -/
theorem pivotal_response_lt_mass_root (p : ℝ) (hfixed : R.reliability p = p)
    (hp : 0 < p) (hp' : p < 1)
    (hblock : ∀ i j, 0 < massPlaneBlock (R.massMatrix p) i j) :
    deriv R.reliability p < positiveRoot (massPlaneBlock (R.massMatrix p)) := by
  have hrow := R.disconnected_mass_score_at_fixed_point p hfixed hp'.ne
  have hc : 0 < R.massMatrix p .single .connected := hblock 1 0
  have hstrict : deriv R.reliability p <
      R.massMatrix p .single .both + R.massMatrix p .single .single := by
    have hpositive := mul_pos (sub_pos.mpr hp') hc
    nlinarith
  have hr := positiveRoot_sub_second_diagonal_pos (massPlaneBlock (R.massMatrix p)) hblock
  change 0 < positiveRoot (massPlaneBlock (R.massMatrix p)) -
    (2 * R.massMatrix p .single .both + R.massMatrix p .single .single) at hr
  linarith [R.massMatrix_nonneg hp.le hp'.le .single .both]

theorem mass_spectral_dominance (p : ℝ) (hfixed : R.reliability p = p)
    (hp : 0 < p) (hp' : p < 1) (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target)
    (hcut : ∀ edge, R.crosses (onlyClosed edge) = true) :
    deriv R.reliability p < (spectralRadius ℂ ((R.massMatrix p).map Complex.ofReal)).toReal ∧
      |secondaryRoot (massPlaneBlock (R.massMatrix p))| <
        (spectralRadius ℂ ((R.massMatrix p).map Complex.ofReal)).toReal := by
  have hblock := (R.massPlaneBlock_pos_of_geometry hp hp' hconnected hscale hcut).1
  have hplane := R.massMatrix_preservesMassPlane p symmetry hs ht
  rw [massPlane_spectralRadius _ (R.massMatrix_nonneg hp.le hp'.le) hplane hblock,
    ENNReal.toReal_ofReal (positiveRoot_pos _ hblock).le]
  exact ⟨R.pivotal_response_lt_mass_root p hfixed hp hp' hblock,
    abs_secondaryRoot_lt_positiveRoot _ hblock⟩

end
end Universality.FiniteNetwork
