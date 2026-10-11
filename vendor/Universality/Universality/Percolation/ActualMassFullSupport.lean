import Universality.Percolation.MassFullSupport

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- Full positive support for the actual same-limit single-terminal law. -/
theorem Classical.internal_single_mass_full_support {rule : Rule} (h : rule.Classical)
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
    x ∈ ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false).map (limit .single)).support := by
  let law (state : LiveState) :=
    (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)
  letI (state : LiveState) := Measure.isProbabilityMeasure_map (hmem state).aestronglyMeasurable.aemeasurable
  have hsupportNonnegative (state : LiveState) : (law state).support ⊆ Set.Ici 0 := by
    apply Measure.support_subset_of_isClosed isClosed_Ici
    change ∀ᵐ y ∂law state, 0 ≤ y
    exact (ae_map_iff (hmem state).aestronglyMeasurable.aemeasurable measurableSet_Ici).mpr (hnonnegative state)
  have hmeanLaw : 0 < ∫ y, y ∂law .connected := by
    rw [show law .connected =
      (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed true).map (limit .connected) from rfl]
    have hmeasurable : AEMeasurable (limit .connected)
        (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed true) := by
      simpa using (hmem .connected).aestronglyMeasurable.aemeasurable
    rw [integral_map hmeasurable (f := fun y : ℝ => y) (by fun_prop)]
    exact hmean
  exact h.mass_smoothing_full_positive_support p hp hp' hfixed law hsupportNonnegative hmeanLaw
    (fun state => h.mass_limit_distribution_smoothing p hp hp' hfixed limit hmem huniform state) x hx

end
end Universality.Rule
