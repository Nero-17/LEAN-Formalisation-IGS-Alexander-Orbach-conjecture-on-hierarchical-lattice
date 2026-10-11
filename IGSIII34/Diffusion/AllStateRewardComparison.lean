import IGSIII34.Diffusion.ActualDegreeRewards
import IGSIII.Mass.RewardNormalization

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory Filter Matrix
open scoped BigOperators Topology

theorem normalized_left_identification
    (matrix basis inverse : Matrix LiveState LiveState ℝ) (eigenvalues right left : LiveState → ℝ)
    (coefficient : ℝ) (coefficientNonzero : coefficient ≠ 0)
    (basisInverse : basis * inverse = 1)
    (rightColumn : right = coefficient • (fun row => basis row .connected))
    (leftEigen : left ᵥ* matrix = eigenvalues .connected • left)
    (normalized : left ⬝ᵥ right = 1)
    (columns : ∀ state, matrix *ᵥ (fun row => basis row state) =
      eigenvalues state • (fun row => basis row state))
    (bothDistinct : eigenvalues .connected ≠ eigenvalues .both)
    (singleDistinct : eigenvalues .connected ≠ eigenvalues .single) :
    ∀ child, left child = inverse .connected child / coefficient := by
  have bothZero := IGSIII.Mass.left_perron_annihilates_remainder matrix left
    (fun row => basis row .both) _ _ bothDistinct leftEigen (columns .both)
  have singleZero := IGSIII.Mass.left_perron_annihilates_remainder matrix left
    (fun row => basis row .single) _ _ singleDistinct leftEigen (columns .single)
  have connectedValue : left ⬝ᵥ (fun row => basis row .connected) = 1 / coefficient := by
    rw [rightColumn, dotProduct_smul] at normalized
    simp only [smul_eq_mul] at normalized
    field_simp [coefficientNonzero]
    nlinarith [normalized]
  have reconstruction : (left ᵥ* basis) ᵥ* inverse = left := by
    rw [Matrix.vecMul_vecMul, basisInverse, Matrix.vecMul_one]
  intro child
  have entry := congrFun reconstruction child
  change (∑ state, (left ᵥ* basis) state * inverse state child) = left child at entry
  rw [sum_liveState] at entry
  change (left ⬝ᵥ (fun row => basis row .connected)) * inverse .connected child +
    (left ⬝ᵥ (fun row => basis row .both)) * inverse .both child +
    (left ⬝ᵥ (fun row => basis row .single)) * inverse .single child = left child at entry
  rw [bothZero, singleZero, connectedValue] at entry
  simpa only [zero_mul, mul_zero, mul_one, add_zero, one_div, div_eq_mul_inv, mul_comm] using entry.symm

/-- The actual edge and birth-vertex rewards are asymptotically proportional
with one deterministic positive constant for *all three conditioned parent
states*. This is a pathwise comparison on their original laws. -/
theorem all_state_edge_vertex_reward_comparison {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ ratio : ℝ, 0 < ratio ∧ ∀ state : LiveState,
      ∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected),
        Tendsto (fun depth =>
          (((rule.generation depth).network.liveCount state .connected
            (Rule.ConfigurationHistory.latest rule depth (path depth)) : ℝ) -
            ratio * Rule.ConfigurationHistory.vertexMass rule state depth path) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
          atTop (𝓝 0) := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have radiusLarge : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint classicalRule.massAdmissible.symmetric classicalRule.scale).2.1
  obtain ⟨perron, remainder, eigenvalue, perronPositive, rewardSplit, perronEigen, remainderEigen, gap⟩ :=
    classicalRule.vertex_reward_spectral_split p positive belowOne
  let right : LiveState → ℝ := (perron .connected)⁻¹ • perron
  have rightNormalized : right .connected = 1 := inv_mul_cancel₀ (perronPositive .connected).ne'
  have rightEigen : rule.network.massMatrix p *ᵥ right = radius • right := by
    change rule.network.massMatrix p *ᵥ ((perron .connected)⁻¹ • perron) = _
    rw [Matrix.mulVec_smul, perronEigen]
    ext state
    simp only [Pi.smul_apply, smul_eq_mul, right, div_eq_mul_inv]
    ring
  obtain ⟨rootLimit, _, rootConvergence, _, _⟩ := classicalRule.positive_population_ae_L2_limit
    p positive belowOne fixedPoint perron perronPositive perronEigen .connected
  have rootPositive := classicalRule.connected_perron_population_positive p positive belowOne fixedPoint
    perron remainder eigenvalue rewardSplit perronEigen remainderEigen gap rootLimit rootConvergence
  have rootRightConvergence : ∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint true,
      Tendsto (fun depth => Rule.ConfigurationHistory.rootLevelPopulation rule .connected right depth path / radius ^ depth)
        atTop (𝓝 (rootLimit path / perron .connected / radius)) := by
    filter_upwards [rootConvergence] with path convergence
    apply Rule.ConfigurationHistory.rootLevelPopulation_tendsto rule .connected right radius radiusLarge path
    convert convergence.const_mul (perron .connected)⁻¹ using 1
    · ext depth
      rw [show right = (perron .connected)⁻¹ • perron from rfl,
        Rule.ConfigurationHistory.weightedPopulation_smul]
      dsimp only [radius]
      ring
    · ring
  obtain ⟨left, leftEigen, leftNormalized, rootCoordinates⟩ := classicalRule.population_vector_limit_from_perron
    p positive belowOne fixedPoint right rightNormalized rightEigen
    (fun path => rootLimit path / perron .connected / radius) rootRightConvergence
  have leftNonnegative : ∀ child, 0 ≤ left child := by
    obtain ⟨path, positiveLimit, coordinates⟩ := (rootPositive.and rootCoordinates).exists
    have scalarPositive : 0 < rootLimit path / perron .connected / radius :=
      div_pos (div_pos positiveLimit (perronPositive .connected)) (zero_lt_one.trans radiusLarge)
    intro child
    have nonnegative : ∀ depth, 0 ≤ Rule.ConfigurationHistory.rootLevelPopulation rule .connected
        (fun state => if state = child then 1 else 0) depth path / radius ^ depth := by
      intro depth
      apply div_nonneg _ (pow_nonneg (zero_lt_one.trans radiusLarge).le _)
      cases depth with
      | zero => simp only [Rule.ConfigurationHistory.rootLevelPopulation_zero]; split_ifs <;> norm_num
      | succ depth => exact (rule.generation depth).network.liveResponse_nonneg _ _ _ (fun state => by split_ifs <;> norm_num)
    have nonnegativeLimit := ge_of_tendsto' (coordinates child) nonnegative
    nlinarith
  have leftPositive := IGSIII.Mass.left_perron_positive_of_positive_power (rule.network.massMatrix p)
    left right radius (zero_lt_one.trans radiusLarge) leftNonnegative leftEigen leftNormalized
    (rule.network.massMatrix_fourth_power_pos p positive belowOne (classicalRule.connected _) classicalRule.scale classicalRule.cut)
  obtain ⟨symmetry, sourceSwap, targetSwap⟩ := classicalRule.massAdmissible.symmetric
  have blockPositive := (rule.network.massPlaneBlock_pos_of_geometry positive belowOne
    (classicalRule.connected _) classicalRule.scale classicalRule.cut).1
  have radiusEquality : radius = positiveRoot (massPlaneBlock (rule.network.massMatrix p)) := by
    dsimp only [radius]
    rw [massPlane_spectralRadius _ (rule.network.massMatrix_nonneg positive.le belowOne.le)
      (rule.network.massMatrix_preservesMassPlane p symmetry sourceSwap targetSwap) blockPositive,
      ENNReal.toReal_ofReal (positiveRoot_pos _ blockPositive).le]
  have dominance := rule.network.mass_spectral_dominance p fixedPoint positive belowOne symmetry
    sourceSwap targetSwap (classicalRule.connected _) classicalRule.scale classicalRule.cut
  obtain ⟨basis, inverse, inverseBasis, basisInverse, diagonalization⟩ :=
    rule.network.massMatrix_real_diagonalization p fixedPoint positive belowOne symmetry sourceSwap targetSwap blockPositive
  have eigenvectors := IGSIII.Mass.diagonalization_eigenvectors _ basis inverse _ inverseBasis basisInverse diagonalization
  have bothDistinct : blockEigenvalues (massPlaneBlock (rule.network.massMatrix p)) (deriv rule.network.reliability p) .both ≠
      blockEigenvalues (massPlaneBlock (rule.network.massMatrix p)) (deriv rule.network.reliability p) .connected := by
    exact ne_of_lt (by simpa only [blockEigenvalues, ← radiusEquality] using
      (le_abs_self (secondaryRoot (massPlaneBlock (rule.network.massMatrix p)))).trans_lt dominance.2)
  have singleDistinct : blockEigenvalues (massPlaneBlock (rule.network.massMatrix p)) (deriv rule.network.reliability p) .single ≠
      blockEigenvalues (massPlaneBlock (rule.network.massMatrix p)) (deriv rule.network.reliability p) .connected := by
    exact ne_of_lt (by simpa only [blockEigenvalues, ← radiusEquality] using dominance.1)
  obtain ⟨coefficient, coefficientNonzero, rightColumn, _, _⟩ := IGSIII.Mass.normalized_left_from_diagonalization
    _ basis inverse _ right inverseBasis basisInverse diagonalization
    (by simpa only [blockEigenvalues, ← radiusEquality] using rightEigen) rightNormalized bothDistinct singleDistinct
  have leftIdentification := normalized_left_identification _ basis inverse _ right left coefficient coefficientNonzero
    basisInverse rightColumn (by simpa only [blockEigenvalues, ← radiusEquality] using leftEigen)
    leftNormalized eigenvectors.1 bothDistinct.symm singleDistinct.symm
  let ratio : ℝ := left .connected * (radius - 1) / perron .connected
  refine ⟨ratio, div_pos (mul_pos (leftPositive .connected) (sub_pos.mpr radiusLarge)) (perronPositive .connected), ?_⟩
  intro state
  have bothZero := classicalRule.subcritical_population_ae_zero p positive belowOne fixedPoint
    (fun row => basis row .both) _ (eigenvectors.1 .both) dominance.2 state
  have singleGap : |deriv rule.network.reliability p| < radius := by
    rw [abs_of_nonneg (rule.network.reliability_derivative_nonneg positive.le belowOne.le)]
    exact dominance.1
  have singleZero := classicalRule.subcritical_population_ae_zero p positive belowOne fixedPoint
    (fun row => basis row .single) _ (eigenvectors.1 .single) singleGap state
  have vertexError := classicalRule.vertex_mass_perron_approximation_ae p positive belowOne fixedPoint
    perron remainder eigenvalue rewardSplit perronEigen remainderEigen gap state
  filter_upwards [bothZero, singleZero, vertexError] with path bothConvergence singleConvergence vertexConvergence
  have result := ((bothConvergence.mul_const (inverse .both .connected)).add
    (singleConvergence.mul_const (inverse .single .connected))).sub (vertexConvergence.const_mul ratio)
  simp only [zero_mul, zero_add, mul_zero, sub_zero] at result
  convert result using 1
  ext depth
  rw [← Rule.ConfigurationHistory.populationVector]
  rw [Rule.ConfigurationHistory.populationVector_eigenbasis_reconstruction rule state basis inverse basisInverse
    right coefficient coefficientNonzero rightColumn depth (path depth) .connected, ← leftIdentification]
  have perronScale : perron = perron .connected • right := by
    ext child
    simp only [Pi.smul_apply, smul_eq_mul, right]
    field_simp [(perronPositive .connected).ne']
  rw [perronScale, Rule.ConfigurationHistory.weightedPopulation_smul]
  dsimp [ratio, radius]
  dsimp only [radius] at radiusLarge
  field_simp [(perronPositive .connected).ne', (sub_pos.mpr radiusLarge).ne']
  rw [← perronScale]
  <;> ring

end
end IGSIII34.Diffusion
