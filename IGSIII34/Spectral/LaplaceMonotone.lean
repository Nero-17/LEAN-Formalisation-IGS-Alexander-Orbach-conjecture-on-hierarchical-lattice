import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The elementary monotonicity step in the Appendix B Tauberian argument.
The heat kernel is an input function here. Its construction is a separate theorem.
-/

set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Set

def diagonalLaplace (kernel : ℝ → ℝ) (parameter : ℝ) : ℝ :=
  ∫ time in Ioi 0, Real.exp (-parameter * time) * kernel time

theorem diagonalLaplace_nonnegative (kernel : ℝ → ℝ) (parameter : ℝ)
    (nonnegative : ∀ time, 0 < time → 0 ≤ kernel time) :
    0 ≤ diagonalLaplace kernel parameter := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with time positive
  exact mul_nonneg (Real.exp_pos _).le (nonnegative time positive)

theorem time_mul_diagonal_le_laplace
    (kernel : ℝ → ℝ) (time : ℝ) (positive : 0 < time)
    (nonnegative : ∀ other, 0 < other → 0 ≤ kernel other)
    (decreasing : AntitoneOn kernel (Ioi 0))
    (integrable : IntegrableOn (fun other => Real.exp (-(time⁻¹) * other) *
      kernel other) (Ioi 0)) :
    time * (Real.exp (-1) * kernel time) ≤ diagonalLaplace kernel time⁻¹ := by
  have subset : Ioc 0 time ⊆ Ioi 0 := fun _ member => member.1
  have pointwise : ∀ᵐ other ∂(volume.restrict (Ioc 0 time)),
      Real.exp (-1) * kernel time ≤
        Real.exp (-(time⁻¹) * other) * kernel other := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with other member
    have exponentBound : (-1 : ℝ) ≤ -(time⁻¹) * other := by
      have bound := mul_le_mul_of_nonneg_left member.2 (inv_nonneg.mpr positive.le)
      rw [inv_mul_cancel₀ positive.ne'] at bound
      linarith
    exact mul_le_mul (Real.exp_le_exp.mpr exponentBound)
      (decreasing member.1 positive member.2)
      (nonnegative time positive) (Real.exp_pos _).le
  have intervalBound := integral_mono_ae
    (integrable_const (Real.exp (-1) * kernel time))
    (integrable.mono_set subset) pointwise
  have mass : volume.real (Ioc 0 time) = time := by
    simp [measureReal_def, Real.volume_Ioc, positive.le]
  have restrictedMass : (volume.restrict (Ioc 0 time)).real univ = time := by
    simpa [measureReal_def] using mass
  rw [integral_const, restrictedMass, smul_eq_mul] at intervalBound
  refine intervalBound.trans ?_
  apply setIntegral_mono_set integrable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with other member
    exact mul_nonneg (Real.exp_pos _).le (nonnegative other member)
  · exact Filter.Eventually.of_forall subset

theorem diagonal_le_exp_mul_laplace_div
    (kernel : ℝ → ℝ) (time : ℝ) (positive : 0 < time)
    (nonnegative : ∀ other, 0 < other → 0 ≤ kernel other)
    (decreasing : AntitoneOn kernel (Ioi 0))
    (integrable : IntegrableOn (fun other => Real.exp (-(time⁻¹) * other) *
      kernel other) (Ioi 0)) :
    kernel time ≤ Real.exp 1 * diagonalLaplace kernel time⁻¹ / time := by
  have bound := time_mul_diagonal_le_laplace kernel time positive nonnegative decreasing integrable
  have multiplied := mul_le_mul_of_nonneg_left bound (Real.exp_pos 1).le
  have cancellation : Real.exp 1 * (time * (Real.exp (-1) * kernel time)) =
      kernel time * time := by
    calc
      _ = (Real.exp 1 * Real.exp (-1)) * (kernel time * time) := by ring
      _ = _ := by rw [← Real.exp_add]; norm_num
  rw [cancellation] at multiplied
  exact (le_div_iff₀ positive).mpr multiplied

theorem diagonalLaplace_tail_le
    (kernel : ℝ → ℝ) (parameter time : ℝ)
    (parameterPositive : 0 < parameter) (timePositive : 0 < time)
    (nonnegative : ∀ other, 0 < other → 0 ≤ kernel other)
    (decreasing : AntitoneOn kernel (Ioi 0))
    (integrable : IntegrableOn (fun other => Real.exp (-parameter * other) *
      kernel other) (Ioi 0)) :
    (∫ other in Ioi time, Real.exp (-parameter * other) * kernel other) ≤
      kernel time / parameter := by
  have subset : Ioi time ⊆ Ioi 0 := fun _ member => timePositive.trans member
  have exponentialIntegrable := integrableOn_exp_mul_Ioi (neg_neg_of_pos parameterPositive) 0
  have constantIntegrable : IntegrableOn
      (fun other => Real.exp (-parameter * other) * kernel time) (Ioi 0) :=
    exponentialIntegrable.mul_const (kernel time)
  have tailBound := integral_mono_ae (integrable.mono_set subset)
    (constantIntegrable.mono_set subset)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with other member
      exact mul_le_mul_of_nonneg_left
        (decreasing timePositive (timePositive.trans member) member.le)
        (Real.exp_pos _).le)
  have enlarged :
      (∫ other in Ioi time, Real.exp (-parameter * other) * kernel time) ≤
        ∫ other in Ioi 0, Real.exp (-parameter * other) * kernel time := by
    apply setIntegral_mono_set (exponentialIntegrable.mul_const (kernel time))
    · exact Filter.Eventually.of_forall (fun other =>
        mul_nonneg (Real.exp_pos _).le (nonnegative time timePositive))
    · exact Filter.Eventually.of_forall subset
  have exponentialIntegral : (∫ other in Ioi 0, Real.exp (-parameter * other)) =
      parameter⁻¹ := by
    rw [integral_exp_mul_Ioi (neg_neg_of_pos parameterPositive)]
    simp
  calc
    _ ≤ _ := tailBound
    _ ≤ _ := enlarged
    _ = _ := by rw [integral_mul_const, exponentialIntegral]; ring

theorem diagonalLaplace_split_le
    (kernel : ℝ → ℝ) (parameter time : ℝ)
    (parameterPositive : 0 < parameter) (timePositive : 0 < time)
    (nonnegative : ∀ other, 0 < other → 0 ≤ kernel other)
    (decreasing : AntitoneOn kernel (Ioi 0))
    (integrable : IntegrableOn (fun other => Real.exp (-parameter * other) *
      kernel other) (Ioi 0))
    (prefixIntegrable : IntegrableOn kernel (Ioc 0 time)) :
    diagonalLaplace kernel parameter ≤
      (∫ other in Ioc 0 time, kernel other) + kernel time / parameter := by
  have prefixSubset : Ioc 0 time ⊆ Ioi 0 := fun _ member => member.1
  have tailSubset : Ioi time ⊆ Ioi 0 := fun _ member => timePositive.trans member
  have partition : Ioc 0 time ∪ Ioi time = Ioi 0 := by
    ext other
    constructor
    · rintro (member | member)
      · exact member.1
      · exact timePositive.trans member
    · intro member
      by_cases before : other ≤ time
      · exact Or.inl ⟨member, before⟩
      · exact Or.inr (lt_of_not_ge before)
  have disjoint : Disjoint (Ioc 0 time) (Ioi time) := by
    apply Set.disjoint_left.mpr
    intro other prefixMember tailMember
    exact (not_lt_of_ge prefixMember.2) tailMember
  have prefixBound := integral_mono_ae (integrable.mono_set prefixSubset) prefixIntegrable
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with other member
      have exponentNonpositive : -parameter * other ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr parameterPositive.le) member.1.le
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (Real.exp_le_one_iff.mpr exponentNonpositive) (nonnegative other member.1))
  unfold diagonalLaplace
  rw [← partition, setIntegral_union disjoint measurableSet_Ioi
    (integrable.mono_set prefixSubset) (integrable.mono_set tailSubset)]
  exact add_le_add prefixBound (diagonalLaplace_tail_le kernel parameter time
    parameterPositive timePositive nonnegative decreasing integrable)

end
end IGSIII34.Spectral
