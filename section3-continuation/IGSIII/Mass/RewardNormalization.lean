import IGSIII.Mass.PositiveVertexMassLimit

set_option autoImplicit false

namespace IGSIII.Mass

open Matrix

/-- A left Perron vector annihilates a right eigenvector with a different
eigenvalue. This identifies the birth-reward coefficient without a limit
normalization assumption. -/
theorem left_perron_annihilates_remainder {State : Type*} [Fintype State]
    (matrix : Matrix State State ℝ) (left remainder : State → ℝ)
    (radius eigenvalue : ℝ) (distinct : radius ≠ eigenvalue)
    (left_eigenvector : left ᵥ* matrix = radius • left)
    (remainder_eigenvector : matrix *ᵥ remainder = eigenvalue • remainder) :
    left ⬝ᵥ remainder = 0 := by
  have equality := dotProduct_mulVec left matrix remainder
  rw [left_eigenvector, remainder_eigenvector, dotProduct_smul, smul_dotProduct] at equality
  change eigenvalue * (left ⬝ᵥ remainder) = radius * (left ⬝ᵥ remainder) at equality
  have product_zero : (radius - eigenvalue) * (left ⬝ᵥ remainder) = 0 := by nlinarith
  exact (mul_eq_zero.mp product_zero).resolve_left (sub_ne_zero.mpr distinct)

/-- The manuscript's coefficient is the left Perron vector paired with the
mean birth reward, divided by `radius - 1`. -/
theorem birth_reward_coefficient {State : Type*} [Fintype State]
    (matrix : Matrix State State ℝ) (left right reward remainder : State → ℝ)
    (radius eigenvalue coefficient : ℝ) (distinct : radius ≠ eigenvalue)
    (left_eigenvector : left ᵥ* matrix = radius • left)
    (remainder_eigenvector : matrix *ᵥ remainder = eigenvalue • remainder)
    (normalized : left ⬝ᵥ right = 1)
    (reward_split : reward = coefficient • right + remainder) :
    (left ⬝ᵥ reward) / (radius - 1) = coefficient / (radius - 1) := by
  rw [reward_split, dotProduct_add, dotProduct_smul, normalized,
    left_perron_annihilates_remainder matrix left remainder radius eigenvalue
      distinct left_eigenvector remainder_eigenvector]
  simp

end IGSIII.Mass

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- A specified actual Perron population limit determines the actual vertex
mass limit on the same sample paths. -/
theorem Classical.vertex_mass_limit_of_population_limit {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (perron remainder : LiveState → ℝ) (eigenvalue : ℝ)
    (reward_split : rule.network.conditionalVertexMass p = perron + remainder)
    (perron_eigenvector : rule.network.massMatrix p *ᵥ perron =
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • perron)
    (remainder_eigenvector : rule.network.massMatrix p *ᵥ remainder = eigenvalue • remainder)
    (spectral_gap : |eigenvalue| < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    (state : LiveState) (limit : (Π n, rule.ConfigurationHistory n) → ℝ)
    (population_limit : ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point
      (state == .connected), Tendsto (fun n => ConfigurationHistory.weightedPopulation rule state perron n (path n) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) atTop (𝓝 (limit path))) :
    ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point (state == .connected),
      Tendsto (fun n => ConfigurationHistory.vertexMass rule state n path /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
        atTop (𝓝 (limit path / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal - 1))) := by
  have approximation := classicalRule.vertex_mass_perron_approximation_ae p positive below_one fixed_point
    perron remainder eigenvalue reward_split perron_eigenvector remainder_eigenvector spectral_gap state
  filter_upwards [approximation, population_limit] with path error_convergence population_convergence
  have combined := error_convergence.add (population_convergence.div_const
    ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal - 1))
  simp only [zero_add] at combined
  convert combined using 1
  ext n
  ring

/-- Strict positivity also holds for the specified Perron population limit
that projects the actual birth reward; it follows from the already established
strictly positive actual vertex limit and almost-sure uniqueness. -/
theorem Classical.connected_perron_population_positive {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (perron remainder : LiveState → ℝ) (eigenvalue : ℝ)
    (reward_split : rule.network.conditionalVertexMass p = perron + remainder)
    (perron_eigenvector : rule.network.massMatrix p *ᵥ perron =
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • perron)
    (remainder_eigenvector : rule.network.massMatrix p *ᵥ remainder = eigenvalue • remainder)
    (spectral_gap : |eigenvalue| < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    (limit : (Π n, rule.ConfigurationHistory n) → ℝ)
    (population_limit : ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
      Tendsto (fun n => ConfigurationHistory.weightedPopulation rule .connected perron n (path n) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n) atTop (𝓝 (limit path))) :
    ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true, 0 < limit path := by
  obtain ⟨vertex_limit, _, vertex_convergence, vertex_positive, _⟩ :=
    classicalRule.internal_connected_vertex_mass_ae_L2_positive p positive below_one fixed_point
  have coupled_convergence := classicalRule.vertex_mass_limit_of_population_limit p positive below_one fixed_point
    perron remainder eigenvalue reward_split perron_eigenvector remainder_eigenvector spectral_gap
    .connected limit population_limit
  have radius_gt_one : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  filter_upwards [vertex_convergence, coupled_convergence, vertex_positive]
    with path vertex_convergence coupled_convergence vertex_positive
  have equality := tendsto_nhds_unique vertex_convergence coupled_convergence
  rw [equality] at vertex_positive
  exact (div_pos_iff_of_pos_right (sub_pos.mpr radius_gt_one)).mp vertex_positive

end Universality.Rule
