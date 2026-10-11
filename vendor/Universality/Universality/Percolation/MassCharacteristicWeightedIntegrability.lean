import Universality.Percolation.MassFourierPolynomialBound
import Universality.Probability.CharacteristicWeightedIntegrability

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- Every polynomial frequency weight is integrable for the characteristic
function of any genuine conditional mass limit. -/
theorem Classical.internal_mass_limit_weighted_integrable {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (state : LiveState) (limit : (Π n, rule.ConfigurationHistory n) → ℝ)
    (hmem : MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)))
    (huniform : ∀ bound, TendstoUniformlyOn
      (fun n t => (rule.generation n).network.conditionalVertexCharacteristic p state
        (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
      (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map limit))
      atTop {t : ℝ | |t| ≤ bound})
    (order : ℕ) :
    Integrable (fun t : ℝ => ‖t‖ ^ order *
      ‖charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map limit) t‖) := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  let characteristic := charFun
    ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map limit)
  letI := Measure.isProbabilityMeasure_map hmem.aestronglyMeasurable.aemeasurable
  have hcontinuous : Continuous characteristic := by
    have heq : characteristic = randomCharacteristic
        (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) limit :=
      funext (fun t => (randomCharacteristic_eq_charFun_map hmem.aestronglyMeasurable t).symm)
    rw [heq]
    exact continuous_randomCharacteristic _ hmem.aestronglyMeasurable
  obtain ⟨constant, hc, depth, hbound⟩ := h.internal_mass_fourier_polynomial_bound p hp hp' hfixed (order + 2)
  apply characteristic_weighted_integrable characteristic hcontinuous.aestronglyMeasurable
    (fun t => norm_charFun_le_one t) order constant hc
  intro t ht
  have hconvergence := (huniform |t|).tendsto_at (x := t) (show |t| ≤ |t| from le_rfl)
  apply le_of_tendsto (hconvergence.norm.mul_const (|t| ^ (order + 2)))
  have hlarge : ∀ᶠ n : ℕ in atTop, |t| + 1 ≤ radius ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hradius).eventually (eventually_ge_atTop (|t| + 1))
  filter_upwards [eventually_ge_atTop depth, hlarge] with n hn hlarge
  apply hbound n hn state t ht
  have hp := pow_pos (zero_lt_one.trans hradius) n
  nlinarith [Real.two_le_pi, abs_nonneg t]

end
end Universality.Rule
