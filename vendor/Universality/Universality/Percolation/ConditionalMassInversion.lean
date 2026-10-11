import Universality.Probability.FiniteLatticeInversion
import Universality.Percolation.ConditionalMassCharacteristic

namespace Universality.FiniteNetwork
noncomputable section
open scoped BigOperators

def conditionalInternalMassProbability {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ)
    (opened sourceSelected targetSelected : Bool) (size : ℕ) : ℝ :=
  ∑ configuration, if R.internalSelectedMass sourceSelected targetSelected configuration = size
    then R.conditionalCellWeight p opened configuration else 0

theorem conditionalInternalCharacteristic_scaled_inversion {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (p : ℝ)
    (opened sourceSelected targetSelected : Bool) (size : ℕ)
    (scale : ℝ) (hscale : 0 < scale) :
    (∫ t in -Real.pi * scale..Real.pi * scale,
      R.conditionalInternalCharacteristic p opened sourceSelected targetSelected (t / scale) *
        Complex.exp (-((t / scale : ℝ) : ℂ) * (size : ℂ) * Complex.I)) =
      (scale : ℂ) * (2 * Real.pi : ℂ) *
        (R.conditionalInternalMassProbability p opened sourceSelected targetSelected size : ℂ) := by
  simpa only [conditionalInternalCharacteristic, conditionalInternalMassProbability,
    Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum, Complex.ofReal_zero,
    apply_ite] using scaled_finite_lattice_fourier_inversion
      (fun configuration => (R.conditionalCellWeight p opened configuration : ℂ))
      (R.internalSelectedMass sourceSelected targetSelected) size scale hscale

end
end Universality.FiniteNetwork
