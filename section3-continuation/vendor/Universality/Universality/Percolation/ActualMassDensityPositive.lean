import Universality.Percolation.ActualMassFullSupport
import Universality.Percolation.AllClosedMassDensityPositive
import Universality.Percolation.MassCharacteristicWeightedIntegrability

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

theorem Classical.internal_single_mass_density_positive {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (limit : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ)
    (hmem : ∀ state, MemLp (limit state) 2
      (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)))
    (hnonnegative : ∀ state, ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected),
      0 ≤ limit state path)
    (hmean : 0 < ∫ path, limit .connected path
      ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed true)
    (huniform : ∀ state bound, TendstoUniformlyOn
      (fun n t => (rule.generation n).network.conditionalVertexCharacteristic p state
        (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
      (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)))
      atTop {t : ℝ | |t| ≤ bound})
    (x : ℝ) (hx : 0 < x) :
    0 < (inverseCharacteristic (charFun
      ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false).map (limit .single))) x).re := by
  let law (state : LiveState) :=
    (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)
  letI (state : LiveState) := Measure.isProbabilityMeasure_map (hmem state).aestronglyMeasurable.aemeasurable
  have hradius : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1)
  have hintegrable : Integrable (charFun (law .single)) := by
    apply (integrable_norm_iff continuous_charFun.aestronglyMeasurable).mp
    simpa only [pow_zero, one_mul] using
      h.internal_mass_limit_weighted_integrable p hp hp' hfixed .single (limit .single) (hmem .single)
        (huniform .single) 0
  apply rule.network.single_density_positive_of_full_support law p _ hp hp' hfixed hradius
    (rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut)
    (h.mass_limit_distribution_smoothing p hp hp' hfixed limit hmem huniform .single) hintegrable
  · exact h.internal_single_mass_full_support p hp hp' hfixed limit hmem hnonnegative hmean huniform
  · exact hx

end
end Universality.Rule
