import IGSIII.Mass.OrientedLeftEigenvector

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork

open Matrix

variable {vertices edges : ℕ}

/-- The mean internal birth reward for each of the four actual terminal masks. -/
noncomputable def orientedMeanVertexReward (network : FiniteNetwork vertices edges) (p : ℝ)
    (parent : MassLiveState) : ℝ :=
  network.conditionalInternalMean p (parent.erase == .connected)
    parent.sourceSelected parent.targetSelected

theorem orientedMeanVertexReward_erase (network : FiniteNetwork vertices edges) (p : ℝ)
    (symmetry : network.NetworkSymmetry)
    (source_swap : symmetry.vertex network.source = network.target)
    (target_swap : symmetry.vertex network.target = network.source) :
    network.orientedMeanVertexReward p = fun state => network.conditionalVertexMass p state.erase := by
  ext parent
  cases parent with
  | connected => rfl
  | both => rfl
  | sourceOnly => rfl
  | targetOnly => exact symmetry.conditionalInternalMean_swap source_swap target_swap p false false true

theorem orientedResponse_nonnegative (network : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (configuration : Configuration edges)
    (values : MassLiveState → ℝ) (nonnegative : ∀ state, 0 ≤ values state) :
    0 ≤ network.orientedResponse sourceSelected targetSelected configuration values := by
  apply Finset.sum_nonneg
  intro edge _
  cases network.orientedChildState sourceSelected targetSelected configuration edge <;>
    simp only [OrientedState.massValue] <;> first | exact nonnegative _ | exact le_rfl

end Universality.FiniteNetwork

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology

/-- The actual four-coordinate root-level mass limit, with one common positive
mean-one random variable and the actual four-mask birth-reward coefficient.
Strict positivity of both one-arm left coordinates is supplied by primitivity. -/
theorem Classical.four_state_mass_limit {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p) :
    ∃ (right left : MassLiveState → ℝ) (coefficient : ℝ)
      (limit : (Π n, rule.ConfigurationHistory n) → ℝ),
      spectralRadius ℂ ((rule.network.orientedMassMatrix p).map Complex.ofReal) =
        spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal) ∧
      right .connected = 1 ∧ (∀ state, 0 < right state) ∧ (∀ state, 0 ≤ left state) ∧
      0 < left .connected ∧ 0 < left .both ∧
      rule.network.orientedMassMatrix p *ᵥ right =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • right ∧
      left ᵥ* rule.network.orientedMassMatrix p =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • left ∧
      left ⬝ᵥ right = 1 ∧ 0 < coefficient ∧
      coefficient = (left ⬝ᵥ rule.network.orientedMeanVertexReward p) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal - 1) ∧
      MemLp limit 2 (ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true) ∧
      (∫ path, limit path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true) = 1 ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true, 0 < limit path) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
        ∀ child : MassLiveState,
        Tendsto (fun n => ConfigurationHistory.rootLevelOrientedPopulation rule
          (fun state => if state = child then 1 else 0) n path /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (limit path * left child))) ∧
      (∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
        Tendsto (fun n => ConfigurationHistory.rootLevelVertexCount rule n path /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (coefficient * limit path))) := by
  obtain ⟨right, left, coefficient, limit, _, normalized, right_positive, left_positive,
    right_eigenvector, left_eigenvector, left_normalized, coefficient_positive, coefficient_formula,
    limit_mem, limit_mean, limit_positive, coordinate_limit, vertex_limit⟩ :=
    classicalRule.three_state_mass_perron p positive below_one fixed_point
  obtain ⟨symmetry, source_swap, target_swap⟩ := classicalRule.massAdmissible.symmetric
  have radius_positive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point
      classicalRule.scale).trans (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  have gap := classicalRule.oriented_mass_gap p positive below_one fixed_point
  have denominator_nonzero :
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal -
        (rule.network.orientedMassMatrix p .sourceOnly .sourceOnly -
          rule.network.orientedMassMatrix p .targetOnly .sourceOnly) ≠ 0 := by
    have bound := (le_abs_self (rule.network.orientedMassMatrix p .sourceOnly .sourceOnly -
      rule.network.orientedMassMatrix p .targetOnly .sourceOnly)).trans_lt gap
    linarith
  have oriented_coordinate_limit := classicalRule.oriented_population_limit_from_three_state p positive below_one
    fixed_point left limit coordinate_limit
  have oriented_left_nonnegative : ∀ child, 0 ≤ orientedLeftLift (rule.network.orientedMassMatrix p)
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) left child := by
    obtain ⟨path, positive_limit, coordinates⟩ := (limit_positive.and oriented_coordinate_limit).exists
    intro child
    have counts_nonnegative (n : ℕ) :
        0 ≤ ConfigurationHistory.rootLevelOrientedPopulation rule
          (fun state => if state = child then 1 else 0) n path /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n := by
      apply div_nonneg _ (pow_nonneg radius_positive.le n)
      cases n with
      | zero => simp only [ConfigurationHistory.rootLevelOrientedPopulation]; split_ifs <;> norm_num
      | succ n =>
        exact (rule.generation n).network.orientedResponse_nonnegative true _ _ _
          (fun state => by split_ifs <;> norm_num)
    have limit_nonnegative := ge_of_tendsto' (coordinates child) counts_nonnegative
    nlinarith
  refine ⟨fun state => right state.erase,
    orientedLeftLift (rule.network.orientedMassMatrix p)
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) left,
    coefficient, limit, (classicalRule.four_type_mass_spectralRadius p positive below_one fixed_point).1,
    normalized, (fun state => right_positive state.erase), oriented_left_nonnegative,
    left_positive .connected, left_positive .both, ?_, ?_, ?_, coefficient_positive, ?_,
    limit_mem, limit_mean, limit_positive, oriented_coordinate_limit, vertex_limit⟩
  · rw [rule.network.orientedMassMatrix_erase_intertwining p symmetry source_swap target_swap right,
      right_eigenvector]
    rfl
  · exact rule.network.orientedLeftLift_eigenvector p _ symmetry source_swap target_swap left
      left_eigenvector denominator_nonzero
  · rw [orientedLeftLift_dotProduct, left_normalized]
  · rw [rule.network.orientedMeanVertexReward_erase p symmetry source_swap target_swap,
      orientedLeftLift_dotProduct]
    exact coefficient_formula

end Universality.Rule
