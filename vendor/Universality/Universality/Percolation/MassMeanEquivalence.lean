import Universality.Percolation.MassEquivalence

namespace Universality.FiniteNetwork
noncomputable section

theorem NetworkEquivalence.conditionalInternalMean {vR eR vS eS : ℕ}
    {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}
    (equivalence : R.NetworkEquivalence S) (p : ℝ) (opened sourceSelected targetSelected : Bool) :
    S.conditionalInternalMean p opened sourceSelected targetSelected =
      R.conditionalInternalMean p opened sourceSelected targetSelected := by
  simpa only [conditionalInternalMoment_one] using
    equivalence.conditionalInternalMoment p opened sourceSelected targetSelected 1

end
end Universality.FiniteNetwork
