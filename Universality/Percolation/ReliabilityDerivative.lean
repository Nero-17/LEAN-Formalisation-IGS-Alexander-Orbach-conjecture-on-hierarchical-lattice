import Universality.Percolation.WheatstoneReliability
import Mathlib.Analysis.Calculus.Deriv.Polynomial

namespace Universality
open Polynomial FiniteNetwork

theorem FiniteNetwork.hasDerivAt_reliability {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ) :
    HasDerivAt R.reliability
      (R.reliabilityPolynomial.derivative.eval₂ (Rat.castHom ℝ) p) p := by
  have h := (R.reliabilityPolynomial.map (Rat.castHom ℝ)).hasDerivAt p
  simpa only [Polynomial.derivative_map, Polynomial.eval_map,
    reliabilityPolynomial_eval] using h

theorem wheatstone_thermal_derivative :
    wheatstoneNetwork.reliabilityPolynomial.derivative.eval₂ (Rat.castHom ℝ) (1 / 2) =
      (13 / 8 : ℝ) := by
  rw [wheatstone_reliabilityPolynomial]
  norm_num [Polynomial.derivative_mul, Polynomial.derivative_sub,
    Polynomial.derivative_add, Polynomial.derivative_X_pow]

theorem wheatstone_hasDerivAt_half :
    HasDerivAt wheatstoneNetwork.reliability (13 / 8) (1 / 2) := by
  simpa only [wheatstone_thermal_derivative] using
    wheatstoneNetwork.hasDerivAt_reliability (1 / 2)

theorem wheatstone_deriv_half :
    deriv wheatstoneNetwork.reliability (1 / 2) = 13 / 8 :=
  wheatstone_hasDerivAt_half.deriv

end Universality
