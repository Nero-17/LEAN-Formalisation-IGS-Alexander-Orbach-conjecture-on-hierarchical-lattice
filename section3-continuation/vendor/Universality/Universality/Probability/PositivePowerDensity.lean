import Universality.Percolation.AllClosedMassDensityPositive
import Mathlib.Topology.Order.Compact

namespace Universality
noncomputable section
open MeasureTheory Filter
open scoped Topology

/-- A finite sum of at least two copies of the actual single-terminal limit has a density
positive everywhere on the positive half-line. -/
theorem inverseCharacteristic_power_positive (measure : Measure ℝ) [IsProbabilityMeasure measure]
    (hintegrable : Integrable (charFun measure))
    (hsupport : ∀ x : ℝ, 0 < x → x ∈ measure.support)
    (count : ℕ) (hcount : 2 ≤ count) :
    Integrable (fun t => charFun measure t ^ count) ∧
      ∀ x : ℝ, 0 < x → 0 < (inverseCharacteristic (fun t => charFun measure t ^ count) x).re := by
  let other := independentSumLaw (fun _ : Fin (count - 1) => measure)
  have hpower : (fun t => charFun measure t ^ count) =
      (fun t => charFun measure t * charFun other t) := by
    funext t
    dsimp only [other]
    rw [independentSumLaw_charFun]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← pow_succ']
    congr 1
    omega
  rw [hpower]
  refine ⟨integrable_charFun_mul_charFun measure other hintegrable, ?_⟩
  intro x hx
  apply inverseCharacteristic_product_positive measure other hintegrable
    (fun y => (inverseCharacteristic_charFun_nonnegative_integrable measure hintegrable).2 y |>.1)
    (measure_eq_withDensity_inverseCharacteristic measure hintegrable) hsupport
  · intro y hy
    exact independent_sum_full_positive_support measure hsupport _ (by omega) y hy
  · exact hx

/-- Uniform lattice approximation to a positive continuous density gives a genuine positive
point lower bound throughout any fixed compact subinterval of the positive half-line. -/
theorem lattice_local_limit_compact_lower
    (probability : ℕ → ℕ → ℝ) (scale : ℕ → ℝ) (hscale : ∀ n, 0 < scale n)
    (limit : ℝ → ℂ) (hintegrable : Integrable limit)
    (hpositive : ∀ x : ℝ, 0 < x → 0 < (inverseCharacteristic limit x).re)
    (hllt : ∀ error > 0, ∀ᶠ n : ℕ in atTop, ∀ size : ℕ,
      ‖(scale n : ℂ) * (probability n size : ℂ) - inverseCharacteristic limit ((size : ℝ) / scale n)‖ < error)
    (left right : ℝ) (hleft : 0 < left) (hinterval : left ≤ right) :
    ∃ lower : ℝ, 0 < lower ∧ ∀ᶠ n : ℕ in atTop, ∀ size : ℕ,
      left ≤ (size : ℝ) / scale n → (size : ℝ) / scale n ≤ right →
        lower / scale n ≤ probability n size := by
  have hcontinuous : Continuous (fun x => (inverseCharacteristic limit x).re) :=
    Complex.continuous_re.comp (continuous_inverseCharacteristic hintegrable)
  obtain ⟨point, hpoint, hminimum⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr hinterval) hcontinuous.continuousOn
  have hpointPositive := hpositive point (hleft.trans_le hpoint.1)
  refine ⟨(inverseCharacteristic limit point).re / 2, half_pos hpointPositive, ?_⟩
  filter_upwards [hllt _ (half_pos hpointPositive)] with n hn
  intro size hfirst hsecond
  have hminimumValue := (isMinOn_iff.mp hminimum) _ ⟨hfirst, hsecond⟩
  have herror := (Complex.abs_re_le_norm
    ((scale n : ℂ) * (probability n size : ℂ) - inverseCharacteristic limit ((size : ℝ) / scale n))).trans_lt (hn size)
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at herror
  apply (div_le_iff₀ (hscale n)).mpr
  have := (abs_lt.mp herror).1
  nlinarith

end
end Universality


