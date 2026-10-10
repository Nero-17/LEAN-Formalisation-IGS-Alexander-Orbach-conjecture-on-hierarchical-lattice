import Universality.Examples.GraphDistances
import Universality.Percolation.OppositeWheatstoneReliability
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace Universality
noncomputable section

theorem Rule.mul_hasDerivAt (outer inner : Rule) (p outerDerivative innerDerivative : ℝ)
    (hfixed : inner.network.reliability p = p)
    (houter : HasDerivAt outer.network.reliability outerDerivative p)
    (hinner : HasDerivAt inner.network.reliability innerDerivative p) :
    HasDerivAt (outer * inner).network.reliability (outerDerivative * innerDerivative) p := by
  have houter' : HasDerivAt outer.network.reliability outerDerivative (inner.network.reliability p) := by
    rwa [hfixed]
  have h := houter'.comp p hinner
  have hfunction : (outer * inner).network.reliability =
      fun p => outer.network.reliability (inner.network.reliability p) := funext (Rule.mul_reliability outer inner)
  rw [hfunction]
  exact h

theorem oppositeWheatstone_hasDerivAt_half :
    HasDerivAt oppositeWheatstoneNetwork.reliability (67 / 32) (1 / 2) := by
  simpa only [oppositeWheatstone_thermal_derivative] using
    oppositeWheatstoneNetwork.hasDerivAt_reliability (1 / 2)

theorem groupedRule_hasDerivAt_half :
    HasDerivAt groupedRule.network.reliability ((871 / 256) ^ 2) (1 / 2) := by
  have first := Rule.mul_hasDerivAt wheatstoneRule wheatstoneRule (1 / 2) _ _
    wheatstone_reliability_half wheatstone_hasDerivAt_half wheatstone_hasDerivAt_half
  have second := Rule.mul_hasDerivAt (wheatstoneRule * wheatstoneRule) oppositeWheatstoneRule (1 / 2) _ _
    oppositeWheatstone_reliability_half first oppositeWheatstone_hasDerivAt_half
  have third := Rule.mul_hasDerivAt ((wheatstoneRule * wheatstoneRule) * oppositeWheatstoneRule)
    oppositeWheatstoneRule (1 / 2) _ _ oppositeWheatstone_reliability_half second oppositeWheatstone_hasDerivAt_half
  norm_num at third ⊢
  exact third

theorem alternatingRule_hasDerivAt_half :
    HasDerivAt alternatingRule.network.reliability ((871 / 256) ^ 2) (1 / 2) := by
  have first := Rule.mul_hasDerivAt wheatstoneRule oppositeWheatstoneRule (1 / 2) _ _
    oppositeWheatstone_reliability_half wheatstone_hasDerivAt_half oppositeWheatstone_hasDerivAt_half
  have second := Rule.mul_hasDerivAt (wheatstoneRule * oppositeWheatstoneRule) wheatstoneRule (1 / 2) _ _
    wheatstone_reliability_half first wheatstone_hasDerivAt_half
  have third := Rule.mul_hasDerivAt ((wheatstoneRule * oppositeWheatstoneRule) * wheatstoneRule)
    oppositeWheatstoneRule (1 / 2) _ _ oppositeWheatstone_reliability_half second oppositeWheatstone_hasDerivAt_half
  norm_num at third ⊢
  exact third

theorem reordered_rules_derivatives :
    deriv groupedRule.network.reliability (1 / 2) = (871 / 256) ^ 2 ∧
      deriv alternatingRule.network.reliability (1 / 2) = (871 / 256) ^ 2 :=
  ⟨groupedRule_hasDerivAt_half.deriv, alternatingRule_hasDerivAt_half.deriv⟩

end
end Universality
