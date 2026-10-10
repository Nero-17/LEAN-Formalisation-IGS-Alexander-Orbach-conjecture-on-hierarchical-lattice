import Universality.Percolation.SubstitutionLaw
import Universality.Percolation.ReliabilityDerivative
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace Universality.FiniteNetwork

theorem hasDerivAt_substitutedReliability
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (p : ℝ) :
    HasDerivAt (R.substitutedReliability S)
      (R.reliabilityPolynomial.derivative.eval₂ (Rat.castHom ℝ) (S.reliability p) *
        S.reliabilityPolynomial.derivative.eval₂ (Rat.castHom ℝ) p) p := by
  have hfunction : R.substitutedReliability S = fun p => R.reliability (S.reliability p) :=
    funext (R.substitutedReliability_eq S)
  rw [hfunction]
  exact HasDerivAt.comp p (R.hasDerivAt_reliability (S.reliability p))
    (S.hasDerivAt_reliability p)

end Universality.FiniteNetwork
