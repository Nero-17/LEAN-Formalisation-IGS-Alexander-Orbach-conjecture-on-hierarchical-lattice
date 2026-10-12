import IGSIII.Mass.ThreeStateMassPerron

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped ENNReal Topology

/-- Statewise vertex masses with the manuscript's single-cell generation zero.
The factor `radius` is required because II's saved histories start with a
substituted rule. The terminal boundary has zero limiting mass. -/
theorem Classical.actual_vertex_mass_expectation_normalization
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ (h : LiveState → ℝ)
      (mass : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ),
      (∀ state, 0 < h state) ∧
      rule.network.massMatrix p *ᵥ h =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • h ∧
      (∀ left : LiveState → ℝ,
        left ᵥ* rule.network.massMatrix p =
          (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • left →
        left ⬝ᵥ h = (left ⬝ᵥ rule.network.conditionalVertexMass p) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal - 1)) ∧
      (∀ state, MemLp (mass state) 2
        (ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected))) ∧
      (∀ state, (∫ path, mass state path
        ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected)) = h state) ∧
      (∀ state, ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected),
        Tendsto (fun n => ConfigurationHistory.vertexMass rule state n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (n + 1))
          atTop (𝓝 (mass state path))) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint true,
        0 < mass .connected path ∧
        Tendsto (fun n => ConfigurationHistory.rootLevelVertexCount rule n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (mass .connected path))) := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have radiusAboveOne : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  have radiusPositive : 0 < radius := zero_lt_one.trans radiusAboveOne
  obtain ⟨perron, remainder, eigenvalue, perronPositive, rewardSplit,
    perronEigenvector, remainderEigenvector, spectralGap⟩ :=
    classicalRule.vertex_reward_spectral_split p positive belowOne
  choose limits limitsMem populationConvergence meanPositive L2Convergence using
    (fun state => classicalRule.positive_population_ae_L2_limit p positive belowOne fixedPoint
      perron perronPositive perronEigenvector state)
  let h : LiveState → ℝ := (radius - 1)⁻¹ • perron
  let mass (state : LiveState) (path : Π n, rule.ConfigurationHistory n) : ℝ :=
    limits state path / ((radius - 1) * radius)
  have means (state : LiveState) :
      (∫ path, limits state path
        ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected)) =
      radius * perron state := by
    obtain ⟨symmetry, sourceSwap, targetSwap⟩ := classicalRule.massAdmissible.symmetric
    exact ConfigurationHistory.population_L2_limit_mean rule p positive belowOne fixedPoint
      symmetry sourceSwap targetSwap perron radius radiusPositive.ne' perronEigenvector state
      (limits state) (limitsMem state) (L2Convergence state)
  have vertexConvergence (state : LiveState) :=
    classicalRule.vertex_mass_limit_of_population_limit p positive belowOne fixedPoint
      perron remainder eigenvalue rewardSplit perronEigenvector remainderEigenvector spectralGap
      state (limits state) (populationConvergence state)
  refine ⟨h, mass, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro state
    exact mul_pos (inv_pos.mpr (sub_pos.mpr radiusAboveOne)) (perronPositive state)
  · dsimp [h]
    rw [Matrix.mulVec_smul, perronEigenvector]
    module
  · intro left leftEigenvector
    have remainderZero := IGSIII.Mass.left_perron_annihilates_remainder
      (rule.network.massMatrix p) left remainder radius eigenvalue
      (ne_of_gt ((le_abs_self eigenvalue).trans_lt spectralGap)) leftEigenvector remainderEigenvector
    rw [rewardSplit, dotProduct_add, remainderZero, add_zero]
    dsimp [h]
    rw [dotProduct_smul]
    simp only [smul_eq_mul, div_eq_mul_inv, mul_comm, radius]
  · intro state
    exact memLp_div_const_real (limitsMem state) _
  · intro state
    change (∫ path, limits state path / ((radius - 1) * radius)
      ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected)) =
      (radius - 1)⁻¹ * perron state
    rw [integral_div, means]
    field_simp [radiusPositive.ne', (sub_pos.mpr radiusAboveOne).ne']
  · intro state
    filter_upwards [vertexConvergence state] with path convergence
    have scaled := convergence.div_const radius
    convert scaled using 1
    · ext n
      rw [pow_succ]
      ring
    · congr 1
      change mass state path = (limits state path / (radius - 1)) / radius
      dsimp [mass]
      field_simp [radiusPositive.ne', (sub_pos.mpr radiusAboveOne).ne']
  · have massPositive := classicalRule.connected_perron_population_positive p positive belowOne fixedPoint
      perron remainder eigenvalue rewardSplit perronEigenvector remainderEigenvector spectralGap
      (limits .connected) (populationConvergence .connected)
    filter_upwards [massPositive, vertexConvergence .connected] with path limitPositive convergence
    refine ⟨div_pos limitPositive (mul_pos (sub_pos.mpr radiusAboveOne) radiusPositive), ?_⟩
    have shifted := ConfigurationHistory.rootLevelVertexCount_tendsto rule radius radiusAboveOne
      path _ convergence
    convert shifted using 1
    congr 1
    change mass .connected path = (limits .connected path / (radius - 1)) / radius
    dsimp [mass]
    field_simp [radiusPositive.ne', (sub_pos.mpr radiusAboveOne).ne']

/-- The same actual root population and vertex count, with the new mass
normalisation. This is a rescaling of the previously certified random variable,
not an additional random field or an assumed target conclusion. -/
theorem Classical.actual_population_vertex_normalization
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ (h v : LiveState → ℝ) (coefficient : ℝ)
      (oldMass mass : (Π n, rule.ConfigurationHistory n) → ℝ),
      (∀ state, 0 < h state) ∧ (∀ state, 0 < v state) ∧
      rule.network.massMatrix p *ᵥ h =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • h ∧
      v ᵥ* rule.network.massMatrix p =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • v ∧
      v ⬝ᵥ h = 1 ∧ 0 < coefficient ∧
      (∀ path, mass path = coefficient * oldMass path) ∧
      MemLp mass 2 (ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint true) ∧
      (∫ path, mass path ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint true) = h .connected ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint true,
        0 < mass path ∧
        (∀ child : LiveState,
          Tendsto (fun n => ConfigurationHistory.rootLevelPopulation rule .connected
            (fun state => if state = child then 1 else 0) n path /
              ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
            atTop (𝓝 (mass path * v child))) ∧
        Tendsto (fun n => ConfigurationHistory.rootLevelVertexCount rule n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (mass path))) := by
  obtain ⟨right, left, coefficient, oldMass, _, rightConnected, rightPositive, leftPositive,
    rightEigenvector, leftEigenvector, normalized, coefficientPositive, _, massMem,
    massMean, massPositive, coordinates, vertices⟩ :=
    classicalRule.three_state_mass_perron p positive belowOne fixedPoint
  let h : LiveState → ℝ := coefficient • right
  let v : LiveState → ℝ := coefficient⁻¹ • left
  let mass (path : Π n, rule.ConfigurationHistory n) := coefficient * oldMass path
  refine ⟨h, v, coefficient, oldMass, mass, ?_, ?_, ?_, ?_, ?_, coefficientPositive,
    fun _ => rfl, massMem.const_smul coefficient, ?_, ?_⟩
  · intro state
    exact mul_pos coefficientPositive (rightPositive state)
  · intro state
    exact mul_pos (inv_pos.mpr coefficientPositive) (leftPositive state)
  · dsimp [h]
    rw [Matrix.mulVec_smul, rightEigenvector]
    module
  · dsimp [v]
    rw [Matrix.smul_vecMul, leftEigenvector]
    module
  · dsimp [v, h]
    rw [smul_dotProduct, dotProduct_smul, normalized]
    simp [coefficientPositive.ne']
  · change (∫ path, coefficient * oldMass path
      ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint true) = coefficient * right .connected
    rw [integral_const_mul, massMean, rightConnected]
  · filter_upwards [massPositive, coordinates, vertices] with path positiveMass populationLimit vertexLimit
    refine ⟨mul_pos coefficientPositive positiveMass, ?_, vertexLimit⟩
    intro child
    convert populationLimit child using 1
    congr 1
    change coefficient * oldMass path * (coefficient⁻¹ * left child) = oldMass path * left child
    field_simp [coefficientPositive.ne']

/-- A single witness for the current manuscript's normalization: every right
Perron coordinate is the expectation of that state's genuine vertex limit;
the same connected vertex limit multiplies the normalized population vector.
The old mean-one field is retained through an almost-sure equality. -/
theorem Classical.actual_expected_mass_population_normalization
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ (h v : LiveState → ℝ) (coefficient : ℝ)
      (mass : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ)
      (oldMass : (Π n, rule.ConfigurationHistory n) → ℝ),
      (∀ state, 0 < h state) ∧ (∀ state, 0 < v state) ∧
      rule.network.massMatrix p *ᵥ h =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • h ∧
      v ᵥ* rule.network.massMatrix p =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • v ∧
      v ⬝ᵥ h = 1 ∧ 0 < coefficient ∧
      (∀ state, MemLp (mass state) 2
        (ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected))) ∧
      (∀ state, (∫ path, mass state path
        ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected)) = h state) ∧
      (∀ state, ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected),
        Tendsto (fun n => ConfigurationHistory.vertexMass rule state n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (n + 1))
          atTop (𝓝 (mass state path))) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint true,
        0 < mass .connected path ∧ mass .connected path = coefficient * oldMass path ∧
        (∀ child : LiveState,
          Tendsto (fun n => ConfigurationHistory.rootLevelPopulation rule .connected
            (fun state => if state = child then 1 else 0) n path /
              ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
            atTop (𝓝 (mass .connected path * v child))) ∧
        Tendsto (fun n => ConfigurationHistory.rootLevelVertexCount rule n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (mass .connected path))) := by
  obtain ⟨h, mass, hPositive, hEigenvector, rewardPairing, massMem, massMeans,
    stateLimits, rootLimit⟩ :=
    classicalRule.actual_vertex_mass_expectation_normalization p positive belowOne fixedPoint
  obtain ⟨right, left, coefficient, oldMass, _, _, _, leftPositive, _, leftEigenvector,
    _, coefficientPositive, coefficientFormula, _, _, _, coordinates, vertices⟩ :=
    classicalRule.three_state_mass_perron p positive belowOne fixedPoint
  let v : LiveState → ℝ := coefficient⁻¹ • left
  refine ⟨h, v, coefficient, mass, oldMass, hPositive, ?_, hEigenvector, ?_, ?_,
    coefficientPositive, massMem, massMeans, stateLimits, ?_⟩
  · intro state
    exact mul_pos (inv_pos.mpr coefficientPositive) (leftPositive state)
  · dsimp [v]
    rw [Matrix.smul_vecMul, leftEigenvector]
    module
  · dsimp [v]
    rw [smul_dotProduct, rewardPairing left leftEigenvector, ← coefficientFormula]
    exact inv_mul_cancel₀ coefficientPositive.ne'
  · filter_upwards [rootLimit, coordinates, vertices] with path rootProperties populationLimit vertexLimit
    have sameMass : mass .connected path = coefficient * oldMass path :=
      tendsto_nhds_unique rootProperties.2 vertexLimit
    refine ⟨rootProperties.1, sameMass, ?_, rootProperties.2⟩
    intro child
    convert populationLimit child using 1
    congr 1
    rw [sameMass]
    change coefficient * oldMass path * (coefficient⁻¹ * left child) = oldMass path * left child
    field_simp [coefficientPositive.ne']

/-- The actual almost-sure vertex limit above is also the actual L² limit,
with the same manuscript depth shift. This transport does not select a new
representative or alter the original probability space. -/
theorem Classical.actual_vertex_mass_L2_of_ae_limit
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (state : LiveState)
    (mass : (Π n, rule.ConfigurationHistory n) → ℝ)
    (massLimit : ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected),
      Tendsto (fun n => ConfigurationHistory.vertexMass rule state n path /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (n + 1))
        atTop (𝓝 (mass path))) :
    Tendsto (fun n => eLpNorm
      ((fun path => ConfigurationHistory.vertexMass rule state n path /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (n + 1)) - mass)
      2 (ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected))) atTop (𝓝 0) := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  obtain ⟨limit, _, convergence, _, convergenceL2⟩ :=
    classicalRule.internal_vertex_mass_ae_L2_limit p positive belowOne fixedPoint state
  have sameMass : mass =ᵐ[ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected)]
      (fun path => limit path / radius) := by
    filter_upwards [massLimit, convergence] with path actualLimit savedLimit
    have divided := savedLimit.div_const radius
    have shifted : Tendsto (fun n => ConfigurationHistory.vertexMass rule state n path / radius ^ (n + 1))
        atTop (𝓝 (limit path / radius)) := by
      convert divided using 1
      ext n
      rw [pow_succ]
      ring
    exact tendsto_nhds_unique actualLimit shifted
  have scaled := L2_zero_smul
    (μ := ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected))
    (fun n => (fun path => ConfigurationHistory.vertexMass rule state n path / radius ^ n) - limit)
    radius⁻¹ convergenceL2
  apply scaled.congr'
  filter_upwards [] with n
  apply eLpNorm_congr_ae
  filter_upwards [sameMass] with path equality
  change radius⁻¹ * (ConfigurationHistory.vertexMass rule state n path / radius ^ n - limit path) =
    ConfigurationHistory.vertexMass rule state n path / radius ^ (n + 1) - mass path
  rw [equality, pow_succ]
  ring

/-- Complete actual mass-normalized three-state conclusion, including L²
vertex convergence and the same almost-sure connected population limit. -/
theorem Classical.actual_expected_mass_L2_population_normalization
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ (h v : LiveState → ℝ)
      (mass : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ),
      (∀ state, 0 < h state) ∧ (∀ state, 0 < v state) ∧
      rule.network.massMatrix p *ᵥ h =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • h ∧
      v ᵥ* rule.network.massMatrix p =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • v ∧
      v ⬝ᵥ h = 1 ∧
      (∀ state, MemLp (mass state) 2
        (ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected))) ∧
      (∀ state, (∫ path, mass state path
        ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected)) = h state) ∧
      (∀ state, Tendsto (fun n => eLpNorm
        ((fun path => ConfigurationHistory.vertexMass rule state n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (n + 1)) - mass state)
        2 (ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected))) atTop (𝓝 0)) ∧
      (∀ state, ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected),
        Tendsto (fun n => ConfigurationHistory.vertexMass rule state n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (n + 1))
          atTop (𝓝 (mass state path))) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint true,
        0 < mass .connected path ∧
        (∀ child : LiveState,
          Tendsto (fun n => ConfigurationHistory.rootLevelPopulation rule .connected
            (fun state => if state = child then 1 else 0) n path /
              ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
            atTop (𝓝 (mass .connected path * v child))) ∧
        Tendsto (fun n => ConfigurationHistory.rootLevelVertexCount rule n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (mass .connected path))) := by
  obtain ⟨h, v, coefficient, mass, oldMass, hPositive, vPositive, hEigenvector,
    vEigenvector, normalized, _, massMem, massMeans, stateLimits, rootLimit⟩ :=
    classicalRule.actual_expected_mass_population_normalization p positive belowOne fixedPoint
  refine ⟨h, v, mass, hPositive, vPositive, hEigenvector, vEigenvector, normalized,
    massMem, massMeans, ?_, stateLimits, ?_⟩
  · intro state
    exact classicalRule.actual_vertex_mass_L2_of_ae_limit p positive belowOne fixedPoint
      state (mass state) (stateLimits state)
  · filter_upwards [rootLimit] with path properties
    exact ⟨properties.1, properties.2.2⟩

end
end Universality.Rule
