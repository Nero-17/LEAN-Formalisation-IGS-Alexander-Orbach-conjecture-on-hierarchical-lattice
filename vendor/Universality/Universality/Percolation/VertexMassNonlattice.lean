import Universality.Percolation.VertexMassNonconstant
import Universality.Probability.CharacteristicNonlattice

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- The actual single-state smoothing relation excludes unit modulus at every
nonzero frequency. Repeated all-closed branches would otherwise force a constant law. -/
theorem Classical.single_mass_smoothing_nonlattice {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (limit : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ)
    (hmem : ∀ state, MemLp (limit state) 2
      (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)))
    (hmean : 0 < (∫ path, limit .single path
      ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false))
    (hsmoothing : ∀ t, charFun
        ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false).map (limit .single)) t =
      ∑ coarse, (rule.network.conditionalCellWeight p false coarse : ℂ) *
        ∏ e, match rule.network.childState .single coarse e with
          | none => 1
          | some child => charFun
            ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map (limit child))
            (t / (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal))
    (t : ℝ) (ht : t ≠ 0) :
    ‖charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false).map (limit .single)) t‖ < 1 := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  let probability := ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false
  have hsingleMem : MemLp (limit .single) 2 probability := hmem .single
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hdegree : rule.network.sourceIncidentEdges.card ≠ 0 := by
    have hb := rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
    omega
  have hnorm (child : LiveState) (frequency : ℝ) :
      ‖charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map
        (limit child)) frequency‖ ≤ 1 := by
    letI := Measure.isProbabilityMeasure_map (hmem child).aestronglyMeasurable.aemeasurable
    exact norm_charFun_le_one _
  by_contra hnot
  have hunit : ‖charFun (probability.map (limit .single)) t‖ = 1 :=
    le_antisymm (hnorm .single t) (le_of_not_gt hnot)
  have hall (n : ℕ) : ‖charFun (probability.map (limit .single)) (t / radius ^ n)‖ = 1 := by
    induction n with
    | zero => simpa using hunit
    | succ n ih =>
      have hbranch := rule.network.allClosed_characteristic_unit_branch p hp hp' hfixed
        (fun child => charFun
          ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map (limit child))
          ((t / radius ^ n) / radius))
        (charFun (probability.map (limit .single)) (t / radius ^ n))
        (fun child => hnorm child _) ih (hsmoothing (t / radius ^ n))
      have hpower := congrArg norm hbranch
      rw [norm_pow, ih] at hpower
      have heq := (pow_eq_one_iff_of_nonneg (norm_nonneg _) hdegree).mp hpower
      have hfrequency : (t / radius ^ n) / radius = t / radius ^ (n + 1) := by
        rw [pow_succ]
        ring
      simpa only [hfrequency, probability, show (LiveState.single == LiveState.connected) = false from rfl] using heq
  have hfrequency : Tendsto (fun n : ℕ => t / radius ^ n) atTop (𝓝 0) := by
    have hz := tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt hradius)
    simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using hz.const_mul t
  have hconstant := ae_constant_of_characteristic_unit_sequence (μ := probability)
    (limit .single) hsingleMem.aestronglyMeasurable (fun n => t / radius ^ n) hfrequency
    (fun n => div_ne_zero ht (pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hradius))))
    (fun n => by rw [randomCharacteristic_eq_charFun_map hsingleMem.aestronglyMeasurable]; exact hall n)
  exact h.single_mass_smoothing_nonconstant p hp hp' hfixed limit hmem hmean hsmoothing hconstant

/-- Nonlattice single-terminal limit for the actual finite mass laws. -/
theorem Classical.internal_single_mass_nonlattice_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ limit : (Π n, rule.ConfigurationHistory n) → ℝ,
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false) ∧
      (∀ t : ℝ, t ≠ 0 →
        ‖charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false).map limit) t‖ < 1) ∧
      ∀ bound : ℝ, TendstoUniformlyOn
        (fun n t => (rule.generation n).network.conditionalInternalCharacteristic p false true false
          (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
        (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed false).map limit))
        atTop {t : ℝ | |t| ≤ bound} := by
  obtain ⟨limit, hmem, _, hmean, huniform, hsmoothing⟩ := h.internal_vertex_mass_smoothing p hp hp' hfixed
  exact ⟨limit .single, hmem .single,
    h.single_mass_smoothing_nonlattice p hp hp' hfixed limit hmem (hmean .single) (hsmoothing .single),
    huniform .single⟩

end
end Universality.Rule
