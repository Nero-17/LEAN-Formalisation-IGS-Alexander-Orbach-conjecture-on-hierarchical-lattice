import IGSIII.Mass.PopulationVector
import IGSIII.Mass.SubcriticalObservable

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace Universality.Rule

open FiniteNetwork Matrix MeasureTheory Filter
open scoped ENNReal Topology

/-- The actual three-state graph population converges coordinatewise to the
left Perron vector on the same paths as a specified normalized Perron limit.
The only probabilistic inputs below are the proved population limit and the
proved vanishing of the two genuine sub-Perron eigen-observables. -/
theorem Classical.population_vector_limit_from_perron {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (below_one : p < 1)
    (fixed_point : rule.network.reliability p = p)
    (right : LiveState → ℝ) (normalized : right .connected = 1)
    (right_eigenvector : rule.network.massMatrix p *ᵥ right =
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • right)
    (limit : (Π n, rule.ConfigurationHistory n) → ℝ)
    (population_limit : ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
      Tendsto (fun n => ConfigurationHistory.rootLevelPopulation rule .connected right n path /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
        atTop (𝓝 (limit path))) :
    ∃ left : LiveState → ℝ,
      left ᵥ* rule.network.massMatrix p =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • left ∧
      left ⬝ᵥ right = 1 ∧
      ∀ᵐ path ∂ConfigurationHistory.infiniteLaw rule p positive below_one fixed_point true,
        ∀ child : LiveState,
        Tendsto (fun n => ConfigurationHistory.rootLevelPopulation rule .connected
          (fun state => if state = child then 1 else 0) n path /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
          atTop (𝓝 (limit path * left child)) := by
  obtain ⟨symmetry, source_swap, target_swap⟩ := classicalRule.massAdmissible.symmetric
  have block_positive := (rule.network.massPlaneBlock_pos_of_geometry positive below_one
    (classicalRule.connected _) classicalRule.scale classicalRule.cut).1
  have spectral_radius : (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal =
      positiveRoot (massPlaneBlock (rule.network.massMatrix p)) := by
    rw [massPlane_spectralRadius _ (rule.network.massMatrix_nonneg positive.le below_one.le)
      (rule.network.massMatrix_preservesMassPlane p symmetry source_swap target_swap) block_positive,
      ENNReal.toReal_ofReal (positiveRoot_pos _ block_positive).le]
  have dominance := rule.network.mass_spectral_dominance p fixed_point positive below_one
    symmetry source_swap target_swap (classicalRule.connected _) classicalRule.scale classicalRule.cut
  have response_gap : |deriv rule.network.reliability p| <
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal := by
    rw [abs_of_nonneg (rule.network.reliability_derivative_nonneg positive.le below_one.le)]
    exact dominance.1
  obtain ⟨basis, inverse, inverse_basis, basis_inverse, diagonalization⟩ :=
    rule.network.massMatrix_real_diagonalization p fixed_point positive below_one
      symmetry source_swap target_swap block_positive
  have eigenvectors := IGSIII.Mass.diagonalization_eigenvectors _ basis inverse _
    inverse_basis basis_inverse diagonalization
  obtain ⟨coefficient, coefficient_nonzero, right_column, left_eigenvector, left_normalized⟩ :=
    IGSIII.Mass.normalized_left_from_diagonalization _ basis inverse _ right
      inverse_basis basis_inverse diagonalization
      (by simpa only [blockEigenvalues, spectral_radius] using right_eigenvector) normalized
      (by exact ne_of_lt (by simpa only [blockEigenvalues, spectral_radius] using
        (le_abs_self (secondaryRoot (massPlaneBlock (rule.network.massMatrix p)))).trans_lt dominance.2))
      (by exact ne_of_lt (by simpa only [blockEigenvalues, spectral_radius] using dominance.1))
  have both_zero := classicalRule.subcritical_population_ae_zero p positive below_one fixed_point
    (fun row => basis row .both) _ (eigenvectors.1 .both) dominance.2 .connected
  have single_zero := classicalRule.subcritical_population_ae_zero p positive below_one fixed_point
    (fun row => basis row .single) _ (eigenvectors.1 .single) response_gap .connected
  have radius_gt_one : 1 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (rule.network.interior_fixed_point_strictly_unstable p positive below_one fixed_point classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive below_one fixed_point
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  refine ⟨fun child => inverse .connected child / coefficient, ?_, left_normalized, ?_⟩
  · simpa only [blockEigenvalues, spectral_radius] using left_eigenvector
  filter_upwards [population_limit, both_zero, single_zero] with path perron_convergence
    both_convergence single_convergence
  have both_root := ConfigurationHistory.rootLevelPopulation_tendsto rule .connected
    (fun row => basis row .both) _ radius_gt_one path 0 both_convergence
  have single_root := ConfigurationHistory.rootLevelPopulation_tendsto rule .connected
    (fun row => basis row .single) _ radius_gt_one path 0 single_convergence
  simp only [zero_div] at both_root single_root
  intro child
  have convergence := ((perron_convergence.mul_const (inverse .connected child / coefficient)).add
    (both_root.mul_const (inverse .both child))).add (single_root.mul_const (inverse .single child))
  simp only [zero_mul, add_zero] at convergence
  apply convergence.congr'
  apply Filter.Eventually.of_forall
  intro n
  cases n with
  | zero =>
    simp only [ConfigurationHistory.rootLevelPopulation_zero, pow_zero, div_one]
    have equality := congrFun (congrFun basis_inverse .connected) child
    simp only [Matrix.mul_apply, sum_liveState, Matrix.one_apply] at equality
    rw [right_column]
    simp only [Pi.smul_apply, smul_eq_mul]
    convert equality using 1 <;> field_simp [coefficient_nonzero]
  | succ n =>
    simp only [ConfigurationHistory.rootLevelPopulation_succ]
    have equality := ConfigurationHistory.populationVector_eigenbasis_reconstruction rule .connected
      basis inverse basis_inverse right coefficient coefficient_nonzero right_column n (path n) child
    have indicator : ConfigurationHistory.weightedPopulation rule .connected
        (fun state => if state = child then 1 else 0) n (path n) =
        ConfigurationHistory.populationVector rule .connected n (path n) child := by
      rw [ConfigurationHistory.weightedPopulation_eq_dotProduct]
      simp [dotProduct]
    rw [indicator, equality]
    ring

end Universality.Rule
