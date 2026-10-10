import Universality.Percolation.IntegerMassProbability
import Universality.Probability.ContinuousDensitySupport
import Universality.Percolation.InternalMassLocalLimit
import Universality.Percolation.InternalMassSmoothDensity

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ContDiff ENNReal

theorem Classical.internal_mass_smooth_integer_local_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ limit : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ,
      ∃ density : LiveState → ℝ → ℝ,
      (∀ state, MemLp (limit state) 2
        (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) ∧
      (∀ state, ContDiff ℝ ∞ (density state)) ∧
      (∀ state x, 0 ≤ density state x) ∧
      (∀ state, Integrable (density state)) ∧
      (∀ state, (∫ x, density state x) = 1) ∧
      (∀ state, (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state) =
        volume.withDensity (fun x => ENNReal.ofReal (density state x))) ∧
      (∀ state x, x < 0 → density state x = 0) ∧
      ∀ state error, 0 < error → ∀ᶠ n : ℕ in atTop, ∀ size : ℤ,
        |((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n *
          (rule.generation n).network.conditionalInternalIntegerMassProbability p
            (state == .connected) true (state == .both) size -
          density state ((size : ℝ) / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)| < error := by
  obtain ⟨limit, hmem, hnonnegative, hmean, huniform, hllt⟩ := h.internal_mass_local_limit p hp hp' hfixed
  let density (state : LiveState) (x : ℝ) := (inverseCharacteristic (charFun
    ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state))) x).re
  have hdensity (state : LiveState) := h.internal_mass_limit_smooth_density p hp hp' hfixed
    state (limit state) (hmem state) (huniform state)
  have hnegative (state : LiveState) (x : ℝ) (hx : x < 0) : density state x = 0 := by
    apply continuous_density_zero_of_negative _ _ (hdensity state).1.continuous
      (hdensity state).2.1 (hdensity state).2.2.2.2 _ x hx
    apply Measure.support_subset_of_isClosed isClosed_Ici
    exact (ae_map_iff (hmem state).aestronglyMeasurable.aemeasurable measurableSet_Ici).mpr (hnonnegative state)
  refine ⟨limit, density, hmem, fun state => (hdensity state).1, fun state => (hdensity state).2.1,
    fun state => (hdensity state).2.2.1, fun state => (hdensity state).2.2.2.1,
    fun state => (hdensity state).2.2.2.2, hnegative, ?_⟩
  intro state error herror
  have hradius : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1)
  filter_upwards [(hllt state).2 error herror] with n hn
  intro size
  by_cases hsize : 0 ≤ size
  · obtain ⟨size, rfl⟩ := Int.eq_ofNat_of_zero_le hsize
    rw [conditionalInternalIntegerMassProbability_natCast]
    have hbound := (Complex.abs_re_le_norm _).trans_lt (hn size)
    simpa only [← Complex.ofReal_pow, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Int.cast_natCast, density] using hbound
  · have hsizeNeg : size < 0 := lt_of_not_ge hsize
    rw [conditionalInternalIntegerMassProbability_negative _ _ _ _ _ _ hsizeNeg,
      mul_zero, hnegative state _ (div_neg_of_neg_of_pos (by exact_mod_cast hsizeNeg) (pow_pos hradius n))]
    simpa using herror

end
end Universality.Rule
