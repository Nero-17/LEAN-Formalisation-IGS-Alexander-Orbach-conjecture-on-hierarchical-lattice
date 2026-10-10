import Universality.Section5.WheatstoneResponse
import Universality.Percolation.ReliabilityDerivative

namespace Universality.Section5
noncomputable section

theorem wheatstoneRule_derivative_half (a b c : Rule)
    (a_fixed : a.network.reliability (1 / 2) = 1 / 2)
    (b_fixed : b.network.reliability (1 / 2) = 1 / 2)
    (c_fixed : c.network.reliability (1 / 2) = 1 / 2) :
    deriv (wheatstoneRule a b c).network.reliability (1 / 2) =
      3 / 4 * deriv a.network.reliability (1 / 2) +
      3 / 4 * deriv b.network.reliability (1 / 2) +
      1 / 8 * deriv c.network.reliability (1 / 2) := by
  have derivativeA := (a.network.hasDerivAt_reliability (1 / 2)).differentiableAt.hasDerivAt
  have derivativeB := (b.network.hasDerivAt_reliability (1 / 2)).differentiableAt.hasDerivAt
  have derivativeC := (c.network.hasDerivAt_reliability (1 / 2)).differentiableAt.hasDerivAt
  have derivative :=
    (((hasDerivAt_const (1 / 2 : ℝ) (1 : ℝ)).sub derivativeC).mul
      (((derivativeA.const_mul 2).mul derivativeB).sub
        ((derivativeA.pow 2).mul (derivativeB.pow 2)))).add
      (derivativeC.mul (((derivativeA.add derivativeB).sub
        (derivativeA.mul derivativeB)).pow 2))
  have response : (wheatstoneRule a b c).network.reliability =
      ((fun _ => 1) - c.network.reliability) *
        ((fun p => 2 * a.network.reliability p) * b.network.reliability -
          a.network.reliability ^ 2 * b.network.reliability ^ 2) +
        c.network.reliability *
          (a.network.reliability + b.network.reliability -
            a.network.reliability * b.network.reliability) ^ 2 := by
    funext p
    exact wheatstoneRule_reliability a b c p
  have formula := derivative.deriv
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply] at formula
  rw [response, formula, a_fixed, b_fixed, c_fixed]
  ring

end
end Universality.Section5
