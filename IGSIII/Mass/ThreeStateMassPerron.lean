import IGSIII.Mass.PopulationVectorLimit

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped ENNReal Topology

/-- The complete three-state mass Perron conclusion for the actual connected
graph histories, in III's root-level indexing. Both Perron vectors are
constructed and strictly positive, the population limit is mean one, and the
vertex coefficient is the left Perron pairing with the actual birth reward.

The orientation of the two one-arm counts is not erased by a theorem claim:
this statement concerns the three actual states of II. -/
theorem Classical.three_state_mass_perron {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    ∃ (right left : LiveState → ℝ) (coefficient : ℝ)
      (limit : (Π n, rule.ConfigurationHistory n) → ℝ),
      (∀ state child, 0 < (rule.network.massMatrix p ^ 4) state child) ∧
      right .connected = 1 ∧ (∀ state, 0 < right state) ∧ (∀ state, 0 < left state) ∧
      rule.network.massMatrix p *ᵥ right =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • right ∧
      left ᵥ* rule.network.massMatrix p =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • left ∧
      left ⬝ᵥ right = 1 ∧ 0 < coefficient ∧
      coefficient = (left ⬝ᵥ rule.network.conditionalVertexMass p) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal - 1) ∧
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true) ∧
      (∫ path, limit path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true) = 1 ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true, 0 < limit path) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
        ∀ child : LiveState,
        Tendsto (fun n : ℕ => ConfigurationHistory.rootLevelPopulation rule .connected
          (fun state => if state = child then 1 else 0) n path /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (limit path * left child))) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
        Tendsto (fun n : ℕ => ConfigurationHistory.rootLevelVertexCount rule n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (coefficient * limit path))) := by
  obtain ⟨right, coefficient, limit, normalized, right_positive, right_eigenvector,
    coefficient_positive, limit_mem, limit_mean, limit_positive, population_limit,
    vertex_limit, coefficient_formula⟩ :=
    classicalRule.normalized_connected_mass_pair p positive below_one fixed_point
  obtain ⟨left, left_eigenvector, left_normalized, coordinate_limit⟩ :=
    classicalRule.population_vector_limit_from_perron p positive below_one fixed_point right
      normalized right_eigenvector limit population_limit
  have radius_positive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive below_one
      fixed_point classicalRule.scale).trans (rule.interior_fixed_point_spectral_dominance p
      positive below_one fixed_point classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  have left_nonnegative : ∀ child, 0 ≤ left child := by
    obtain ⟨path, positive_limit, coordinate_convergence⟩ := (limit_positive.and coordinate_limit).exists
    intro child
    have counts_nonnegative (n : ℕ) :
        0 ≤ ConfigurationHistory.rootLevelPopulation rule .connected
          (fun state => if state = child then 1 else 0) n path /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n := by
      apply div_nonneg _ (pow_nonneg radius_positive.le n)
      cases n with
      | zero =>
        simp only [ConfigurationHistory.rootLevelPopulation_zero]
        split_ifs <;> norm_num
      | succ n =>
        exact (rule.generation n).network.liveResponse_nonneg .connected _ _
          (fun state => by split_ifs <;> norm_num)
    have nonnegative_limit := ge_of_tendsto' (coordinate_convergence child) counts_nonnegative
    nlinarith
  have primitive := rule.network.massMatrix_fourth_power_pos p positive below_one
    (classicalRule.connected _) classicalRule.scale classicalRule.cut
  have left_positive := IGSIII.Mass.left_perron_positive_of_positive_power _ left right _
    radius_positive left_nonnegative left_eigenvector left_normalized primitive
  exact ⟨right, left, coefficient, limit, primitive, normalized, right_positive, left_positive,
    right_eigenvector, left_eigenvector, left_normalized, coefficient_positive,
    coefficient_formula left left_eigenvector left_normalized, limit_mem, limit_mean,
    limit_positive, coordinate_limit, vertex_limit⟩

end Universality.Rule
