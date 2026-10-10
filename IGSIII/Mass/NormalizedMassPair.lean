import IGSIII.Mass.RootLevel

set_option autoImplicit false

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- The actual connected root-level process admits a Perron weight normalized
at the connected type, a mean-one strictly positive population limit, and a
deterministic positive vertex-reward coefficient. The coefficient agrees with
the manuscript's left-Perron formula whenever `left · right = 1`.

This is a scalar population statement for II's three live states. The four
oriented type counts and retained-component cylinder coupling are separate. -/
theorem Classical.normalized_connected_mass_pair {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    ∃ (right : LiveState → ℝ) (coefficient : ℝ) (limit : (Π n, rule.ConfigurationHistory n) → ℝ),
      right .connected = 1 ∧ (∀ state, 0 < right state) ∧
      rule.network.massMatrix p *ᵥ right =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • right ∧
      0 < coefficient ∧
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true) ∧
      (∫ path, limit path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true) = 1 ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true, 0 < limit path) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
        Tendsto (fun n => ConfigurationHistory.rootLevelPopulation rule .connected right n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) atTop (𝓝 (limit path))) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
        Tendsto (fun n => ConfigurationHistory.rootLevelVertexCount rule n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (coefficient * limit path))) ∧
      ∀ left : LiveState → ℝ,
        left ᵥ* rule.network.massMatrix p =
          (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • left →
        left ⬝ᵥ right = 1 →
        coefficient = (left ⬝ᵥ rule.network.conditionalVertexMass p) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal - 1) := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have radius_gt_one : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  have radius_positive : 0 < radius := zero_lt_one.trans radius_gt_one
  obtain ⟨perron, remainder, eigenvalue, perron_positive, reward_split,
      perron_eigenvector, remainder_eigenvector, spectral_gap⟩ :=
    classicalRule.vertex_reward_spectral_split p positive below_one
  obtain ⟨population_limit, population_mem, population_ae, _, population_L2⟩ :=
    classicalRule.positive_population_ae_L2_limit p positive below_one fixed_point
      perron perron_positive perron_eigenvector .connected
  have population_positive := classicalRule.connected_perron_population_positive p positive below_one fixed_point
    perron remainder eigenvalue reward_split perron_eigenvector remainder_eigenvector spectral_gap
    population_limit population_ae
  have vertex_ae := classicalRule.vertex_mass_limit_of_population_limit p positive below_one fixed_point
    perron remainder eigenvalue reward_split perron_eigenvector remainder_eigenvector spectral_gap
    .connected population_limit population_ae
  let right : LiveState → ℝ := (perron .connected)⁻¹ • perron
  let limit (path : Π n, rule.ConfigurationHistory n) := population_limit path / (perron .connected * radius)
  have rescale_perron : perron = perron .connected • right := by
    ext state
    change perron state = perron .connected * ((perron .connected)⁻¹ * perron state)
    field_simp [(perron_positive .connected).ne']
  refine ⟨right, perron .connected / (radius - 1), limit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (perron .connected)⁻¹ * perron .connected = 1
    exact inv_mul_cancel₀ (perron_positive .connected).ne'
  · intro state
    exact mul_pos (inv_pos.mpr (perron_positive .connected)) (perron_positive state)
  · change rule.network.massMatrix p *ᵥ ((perron .connected)⁻¹ • perron) =
      radius • ((perron .connected)⁻¹ • perron)
    rw [Matrix.mulVec_smul, perron_eigenvector]
    module
  · exact div_pos (perron_positive .connected) (sub_pos.mpr radius_gt_one)
  · exact memLp_div_const_real population_mem _
  · change (∫ path, population_limit path / (perron .connected * radius)
      ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true) = 1
    rw [integral_div]
    obtain ⟨symmetry, source_swap, target_swap⟩ := classicalRule.massAdmissible.symmetric
    have mean := ConfigurationHistory.population_L2_limit_mean rule p positive below_one fixed_point
      symmetry source_swap target_swap perron radius radius_positive.ne' perron_eigenvector .connected
      population_limit population_mem population_L2
    simp only [beq_self_eq_true] at mean
    rw [mean]
    field_simp [(perron_positive .connected).ne', radius_positive.ne']
  · filter_upwards [population_positive] with path positive_limit
    exact div_pos positive_limit (mul_pos (perron_positive .connected) radius_positive)
  · filter_upwards [population_ae] with path convergence
    have scaled := convergence.const_mul (perron .connected)⁻¹
    have weighted : Tendsto
        (fun n => ConfigurationHistory.weightedPopulation rule .connected right n (path n) / radius ^ n)
        atTop (𝓝 ((perron .connected)⁻¹ * population_limit path)) := by
      convert scaled using 1
      ext n
      rw [show right = (perron .connected)⁻¹ • perron from rfl,
        ConfigurationHistory.weightedPopulation_smul]
      ring
    have shifted := ConfigurationHistory.rootLevelPopulation_tendsto rule .connected right radius
      radius_gt_one path _ weighted
    convert shifted using 1
    congr 1
    dsimp [limit]
    ring
  · filter_upwards [vertex_ae] with path convergence
    have shifted := ConfigurationHistory.rootLevelVertexCount_tendsto rule radius radius_gt_one path _ convergence
    convert shifted using 1
    congr 1
    change perron .connected / (radius - 1) * (population_limit path / (perron .connected * radius)) =
      (population_limit path / (radius - 1)) / radius
    field_simp [(perron_positive .connected).ne', radius_positive.ne', (sub_pos.mpr radius_gt_one).ne']
  · intro left left_eigenvector normalized
    apply (IGSIII.Mass.birth_reward_coefficient (rule.network.massMatrix p) left right
      (rule.network.conditionalVertexMass p) remainder radius eigenvalue (perron .connected)
      (ne_of_gt ((le_abs_self eigenvalue).trans_lt spectral_gap)) left_eigenvector
      remainder_eigenvector normalized _).symm
    rw [← rescale_perron]
    exact reward_split

end Universality.Rule
