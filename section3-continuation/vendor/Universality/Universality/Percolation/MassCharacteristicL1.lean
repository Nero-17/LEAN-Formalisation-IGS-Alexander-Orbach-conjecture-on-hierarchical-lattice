import Universality.Percolation.MassFourierPolynomialBound
import Universality.Probability.TruncatedFourierL1

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- The true finite conditional mass laws converge in Fourier L1 after
truncation to their expanding fundamental lattice intervals. -/
theorem Classical.internal_mass_truncated_characteristic_L1 {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p) :
    ∃ limit : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ,
      (∀ state, MemLp (limit state) 2
        (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) ∧
      (∀ state, ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected),
        0 ≤ limit state path) ∧
      (∀ state, 0 < ∫ path, limit state path
        ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
      (∀ state bound, TendstoUniformlyOn
        (fun n t => (rule.generation n).network.conditionalVertexCharacteristic p state
          (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
        (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)))
        atTop {t : ℝ | |t| ≤ bound}) ∧
      ∀ state,
        Integrable (charFun
          ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state))) ∧
        Tendsto (fun n => ∫ t : ℝ,
          ‖(Set.Ioc
              (-Real.pi * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
              (Real.pi * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)).indicator
            (fun frequency => (rule.generation n).network.conditionalVertexCharacteristic p state
              (frequency / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)) t -
            charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)) t‖)
          atTop (𝓝 0) := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  obtain ⟨limit, hmem, hnonnegative, hmean, huniform, _⟩ := h.internal_vertex_mass_smoothing p hp hp' hfixed
  obtain ⟨constant, hc, depth, hquadratic⟩ := h.internal_mass_fourier_polynomial_bound p hp hp' hfixed 2
  refine ⟨limit, hmem, hnonnegative, hmean, huniform, ?_⟩
  intro state
  apply truncated_fourier_L1_convergence
    (fun n t => (rule.generation n).network.conditionalVertexCharacteristic p state (t / radius ^ n))
    (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)))
    radius constant hradius hc
  · intro n
    exact ((rule.generation n).network.continuous_conditionalVertexCharacteristic p state).comp
      (by fun_prop) |>.aestronglyMeasurable
  · have heq : charFun
        ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)) =
        randomCharacteristic (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) (limit state) :=
      funext (fun t => (randomCharacteristic_eq_charFun_map (hmem state).aestronglyMeasurable t).symm)
    rw [heq]
    exact (continuous_randomCharacteristic _ (hmem state).aestronglyMeasurable).aestronglyMeasurable
  · intro t
    exact (huniform state |t|).tendsto_at (x := t) (show |t| ≤ |t| from le_rfl)
  · intro n t
    exact (rule.generation n).network.norm_conditionalInternalCharacteristic_le_one p hp.le hp'.le
      (by rwa [rule.generation_fixed_point p hfixed n]) (by rwa [rule.generation_fixed_point p hfixed n]) _ _ _ _
  · filter_upwards [eventually_ge_atTop depth] with n hn
    exact hquadratic n hn state

end
end Universality.Rule
