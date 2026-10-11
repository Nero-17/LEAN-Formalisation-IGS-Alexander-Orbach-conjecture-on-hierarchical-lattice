import Universality.Percolation.MassSupportBranches
import Universality.Probability.CharacteristicDensity
import Universality.Probability.ContinuousDensityDomination
import Universality.Probability.InverseCharacteristicPositiveConvolution

namespace Universality
noncomputable section
open MeasureTheory
open scoped ENNReal

theorem finiteMixtureLaw_component_le {index : Type*} [Fintype index]
    (weight : index → ℝ) (law : index → Measure ℝ) (chosen : index) :
    ENNReal.ofReal (weight chosen) • law chosen ≤ finiteMixtureLaw weight law := by
  classical
  apply Measure.le_iff.mpr
  intro region _
  simp only [finiteMixtureLaw, Measure.coe_finset_sum, Finset.sum_apply]
  exact Finset.single_le_sum (f := fun i => (ENNReal.ofReal (weight i) • law i) region)
    (fun i _ => bot_le) (Finset.mem_univ chosen)

theorem independent_sum_full_positive_support (measure : Measure ℝ) [IsProbabilityMeasure measure]
    (hsupport : ∀ x : ℝ, 0 < x → x ∈ measure.support) (count : ℕ) (hcount : 0 < count)
    (x : ℝ) (hx : 0 < x) :
    x ∈ (independentSumLaw (fun _ : Fin count => measure)).support := by
  have hcountReal : (0 : ℝ) < count := by exact_mod_cast hcount
  have h := independent_sum_support (fun _ : Fin count => measure) (fun _ => x / count)
    (fun _ => hsupport _ (div_pos hx hcountReal))
  simpa [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀ x hcountReal.ne'] using h

end
end Universality

namespace Universality.FiniteNetwork
noncomputable section
open MeasureTheory
open scoped ENNReal

theorem single_density_positive_of_full_support {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (p radius : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : R.reliability p = p)
    (hradius : 0 < radius) (hdegree : 2 ≤ R.sourceIncidentEdges.card)
    (hsmoothing : law .single = finiteMixtureLaw (R.conditionalCellWeight p false)
      (R.offspringMassLaw law radius .single))
    (hintegrable : Integrable (charFun (law .single)))
    (hsupport : ∀ x : ℝ, 0 < x → x ∈ (law .single).support)
    (x : ℝ) (hx : 0 < x) :
    0 < (inverseCharacteristic (charFun (law .single)) x).re := by
  let other := independentSumLaw (fun _ : Fin (R.sourceIncidentEdges.card - 1) => law .single)
  let branch := R.offspringMassLaw law radius .single (fun _ => false)
  have hproduct : charFun branch = (fun t =>
      (charFun (law .single) (t / radius)) * charFun other (t / radius)) := by
    funext t
    rw [show branch = R.offspringMassLaw law radius .single (fun _ => false) from rfl,
      R.offspringMassLaw_allClosed_single, charFun_map_mul, independentSumLaw_charFun]
    dsimp only [other]
    rw [independentSumLaw_charFun]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have hfrequency : radius⁻¹ * t = t / radius := by ring
    rw [hfrequency]
    rw [← pow_succ']
    congr 1
    omega
  have hproductIntegrable := integrable_charFun_mul_charFun (law .single) other hintegrable
  have hbranchIntegrable : Integrable (charFun branch) := by
    rw [hproduct]
    simpa only [div_eq_mul_inv] using hproductIntegrable.comp_mul_right' (inv_ne_zero hradius.ne')
  have hbranchPositive : 0 < (inverseCharacteristic (charFun branch) x).re := by
    rw [hproduct, inverseCharacteristic_comp_div (fun t => charFun (law .single) t * charFun other t)
      radius hradius x]
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    apply mul_pos hradius
    apply inverseCharacteristic_product_positive (law .single) other hintegrable
      (fun y => (inverseCharacteristic_charFun_nonnegative_integrable (law .single) hintegrable).2 y |>.1)
      (measure_eq_withDensity_inverseCharacteristic (law .single) hintegrable) hsupport
    · intro y hy
      exact independent_sum_full_positive_support (law .single) hsupport _ (by omega) y hy
    · exact mul_pos hradius hx
  have hdomination : ENNReal.ofReal (R.conditionalCellWeight p false (fun _ => false)) • branch ≤ law .single := by
    rw [hsmoothing]
    exact finiteMixtureLaw_component_le _ _ (fun _ => false)
  have hpointwise := continuous_density_weighted_le branch (law .single)
    (fun y => (inverseCharacteristic (charFun branch) y).re)
    (fun y => (inverseCharacteristic (charFun (law .single)) y).re)
    (R.conditionalCellWeight p false (fun _ => false))
    (R.conditionalCellWeight_allClosed_pos p hp hp' hfixed).le
    (Complex.continuous_re.comp (continuous_inverseCharacteristic hbranchIntegrable))
    (Complex.continuous_re.comp (continuous_inverseCharacteristic hintegrable))
    (fun y => (inverseCharacteristic_charFun_nonnegative_integrable (law .single) hintegrable).2 y |>.1)
    (measure_eq_withDensity_inverseCharacteristic branch hbranchIntegrable)
    (measure_eq_withDensity_inverseCharacteristic (law .single) hintegrable) hdomination x
  exact (mul_pos (R.conditionalCellWeight_allClosed_pos p hp hp' hfixed) hbranchPositive).trans_le hpointwise

end
end Universality.FiniteNetwork
