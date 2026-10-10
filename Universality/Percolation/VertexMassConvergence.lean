import Universality.Percolation.VertexMassPerronApproximation
import Universality.Percolation.PositivePopulationLimit

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- The actual internal vertex mass, on the coherent conditional configuration
space, has a nonzero L² limit at the genuine spectral scale. -/
theorem Classical.internal_vertex_mass_L2_limit {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (state : LiveState) :
    ∃ limit : (Π n, rule.ConfigurationHistory n) → ℝ,
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
      0 < (∫ path, limit path ∂ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)) ∧
      Tendsto (fun n => eLpNorm
        ((fun path => ConfigurationHistory.vertexMass rule state n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) - limit)
        2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) atTop (𝓝 0) := by
  let probability := ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  obtain ⟨perron, remainder, eigenvalue, hpositive, hsplit, hperron, hremainder, hgap⟩ :=
    h.vertex_reward_spectral_split p hp hp'
  obtain ⟨limit, hlimit, hmean, hconv⟩ := h.positive_population_L2_limit p hp hp' hfixed perron hpositive hperron state
  refine ⟨(radius - 1)⁻¹ • limit, hlimit.const_smul _, ?_, ?_⟩
  · change 0 < ∫ path, (radius - 1)⁻¹ * limit path ∂probability
    rw [integral_const_mul]
    exact mul_pos (inv_pos.mpr (sub_pos.mpr hradius)) hmean
  · let population (n : ℕ) (path : Π k, rule.ConfigurationHistory k) :=
      ConfigurationHistory.weightedPopulation rule state perron n (path n)
    have hpopMem (n : ℕ) : MemLp (population n) 2 probability :=
      ConfigurationHistory.memLp_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
        (ConfigurationHistory.weightedPopulation rule state perron n) 2
    let error (n : ℕ) (path : Π k, rule.ConfigurationHistory k) :=
      (ConfigurationHistory.vertexMass rule state n path - population n path / (radius - 1)) / radius ^ n
    have herrorMeas (n : ℕ) : AEStronglyMeasurable (error n) probability :=
      (memLp_div_const_real ((ConfigurationHistory.memLp_vertexMass rule p hp hp' hfixed state n 2).sub
        (memLp_div_const_real (hpopMem n) (radius - 1))) (radius ^ n)).aestronglyMeasurable
    have herror : Tendsto (fun n => eLpNorm (error n) 2 probability) atTop (𝓝 0) :=
      h.vertex_mass_perron_approximation p hp hp' hfixed perron remainder eigenvalue hsplit hperron hremainder hgap state
    let difference (n : ℕ) := (fun path => population n path / radius ^ n) - limit
    have hdifferenceMeas (n : ℕ) : AEStronglyMeasurable ((radius - 1)⁻¹ • difference n) probability :=
      (((memLp_div_const_real (hpopMem n) (radius ^ n)).sub hlimit).const_smul _).aestronglyMeasurable
    have hscaled := L2_zero_smul (μ := probability) difference (radius - 1)⁻¹ hconv
    have hcombined := L2_zero_add (μ := probability) error (fun n => (radius - 1)⁻¹ • difference n)
      herrorMeas hdifferenceMeas herror hscaled
    have heq (n : ℕ) : error n + (radius - 1)⁻¹ • difference n =
        (fun path => ConfigurationHistory.vertexMass rule state n path / radius ^ n) - (radius - 1)⁻¹ • limit := by
      funext path
      change error n path + (radius - 1)⁻¹ * (population n path / radius ^ n - limit path) =
        ConfigurationHistory.vertexMass rule state n path / radius ^ n - (radius - 1)⁻¹ * limit path
      dsimp [error]
      ring
    exact hcombined.congr' (Eventually.of_forall (fun n =>
      congrArg (fun g : (Π k, rule.ConfigurationHistory k) → ℝ => eLpNorm g 2 probability) (heq n)))

end
end Universality.Rule
