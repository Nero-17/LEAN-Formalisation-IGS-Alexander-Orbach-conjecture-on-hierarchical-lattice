import Universality.Arithmetic.GraphFixedPointCoefficients
import Universality.Arithmetic.GraphFixedPointParity

namespace Universality.Rule

open Polynomial FiniteNetwork

/-- No prime reduction of the complete fixed-point quotient is constant.
The characteristic-two obstruction is discharged by the actual graph involution. -/
theorem Classical.fixedPointPolynomial_mod_prime_nonconstant {rule : Rule}
    (h : rule.Classical) (prime : ℕ) (hprime : prime.Prime) :
    ((rule.network.integerFixedPointPolynomial (h.connected _)).map
      (Int.castRingHom (ZMod prime))).natDegree ≠ 0 := by
  apply rule.network.integerFixedPointPolynomial_mod_prime_nonconstant_of_mod_two
    (h.connected _) h.scale h.cut
  exact rule.network.integerFixedPointPolynomial_mod_two_nonconstant_of_parity
    (h.connected _) h.scale h.cut h.two_edge_configuration_parity
  exact hprime

end Universality.Rule

#print axioms Universality.Rule.Classical.fixedPointPolynomial_mod_prime_nonconstant
