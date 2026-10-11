import Universality.Percolation.ConditionalMassInversion

namespace Universality.FiniteNetwork
noncomputable section

def conditionalInternalIntegerMassProbability {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ)
    (opened sourceSelected targetSelected : Bool) (size : ℤ) : ℝ :=
  ∑ configuration, if (R.internalSelectedMass sourceSelected targetSelected configuration : ℤ) = size
    then R.conditionalCellWeight p opened configuration else 0

theorem conditionalInternalIntegerMassProbability_natCast {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ)
    (opened sourceSelected targetSelected : Bool) (size : ℕ) :
    R.conditionalInternalIntegerMassProbability p opened sourceSelected targetSelected (size : ℤ) =
      R.conditionalInternalMassProbability p opened sourceSelected targetSelected size := by
  simp only [conditionalInternalIntegerMassProbability, conditionalInternalMassProbability, Nat.cast_inj]

theorem conditionalInternalIntegerMassProbability_negative {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ)
    (opened sourceSelected targetSelected : Bool) (size : ℤ) (hsize : size < 0) :
    R.conditionalInternalIntegerMassProbability p opened sourceSelected targetSelected size = 0 := by
  apply Finset.sum_eq_zero
  intro configuration _
  apply if_neg
  have hnonnegative : (0 : ℤ) ≤ R.internalSelectedMass sourceSelected targetSelected configuration :=
    Int.natCast_nonneg _
  omega

end
end Universality.FiniteNetwork
