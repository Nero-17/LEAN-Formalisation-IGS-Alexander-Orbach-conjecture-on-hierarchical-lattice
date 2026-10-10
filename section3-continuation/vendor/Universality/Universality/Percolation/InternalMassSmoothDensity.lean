import Universality.Percolation.MassCharacteristicWeightedIntegrability
import Universality.Probability.CharacteristicDensity
import Universality.Probability.SmoothInverseCharacteristic

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ContDiff

/-- Every actual conditional mass limit has a nonnegative smooth density given
by Fourier inversion; the same limit witness may be used in the local limit. -/
theorem Classical.internal_mass_limit_smooth_density {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (state : LiveState) (limit : (Π n, rule.ConfigurationHistory n) → ℝ)
    (hmem : MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)))
    (huniform : ∀ bound, TendstoUniformlyOn
      (fun n t => (rule.generation n).network.conditionalVertexCharacteristic p state
        (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
      (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map limit))
      atTop {t : ℝ | |t| ≤ bound}) :
    let density := fun x : ℝ => (inverseCharacteristic (charFun
      ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map limit)) x).re
    ContDiff ℝ ∞ density ∧ (∀ x, 0 ≤ density x) ∧ Integrable density ∧
      (∫ x, density x) = 1 ∧
      (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map limit =
        volume.withDensity (fun x => ENNReal.ofReal (density x)) := by
  dsimp only
  letI := Measure.isProbabilityMeasure_map hmem.aestronglyMeasurable.aemeasurable
  have hweighted := h.internal_mass_limit_weighted_integrable p hp hp' hfixed state limit hmem huniform
  have hintegrable : Integrable (charFun
      ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map limit)) := by
    exact (integrable_norm_iff continuous_charFun.aestronglyMeasurable).mp
      (by simpa using hweighted 0)
  have hinverse := inverseCharacteristic_charFun_nonnegative_integrable _ hintegrable
  have hsmooth : ContDiff ℝ ∞ (inverseCharacteristic (charFun
      ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map limit))) :=
    contDiff_inverseCharacteristic (fun n _ => hweighted n)
  refine ⟨?_, fun x => (hinverse.2 x).1, hinverse.1.re,
    inverseCharacteristic_charFun_integral_one _ hintegrable,
    measure_eq_withDensity_inverseCharacteristic _ hintegrable⟩
  exact Complex.reCLM.contDiff.comp hsmooth

end
end Universality.Rule
