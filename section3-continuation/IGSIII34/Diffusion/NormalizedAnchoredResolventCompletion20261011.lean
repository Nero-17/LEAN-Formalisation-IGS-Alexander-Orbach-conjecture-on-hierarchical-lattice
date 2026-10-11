import IGSIII34.Spectral.AnchoredResolventCompletion20261011
import IGSIII34.Diffusion.CompactL2UniformCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace IGSIII34.Diffusion
noncomputable section
open IGSIII34.Spectral InnerProductSpace MeasureTheory Filter
open scoped Topology

variable {Energy L2 : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]

def parameterAnchoredResolventBilinearCompletion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (parameter : ℝ) : Energy →L[ℝ] Energy →L[ℝ] ℝ :=
  anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation +
    (parameter - 1) • ((innerSL ℝ).comp (embedding.adjoint.comp embedding))

theorem parameterAnchoredResolventBilinear_apply_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (parameter : ℝ) (first second : Energy) :
    parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter first second =
      inner ℝ first second - anchorEvaluation first * anchorEvaluation second +
        parameter * inner ℝ (embedding first) (embedding second) := by
  simp only [parameterAnchoredResolventBilinearCompletion20261011, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [anchoredResolventBilinear_apply_completion20261011]
  change inner ℝ first second - anchorEvaluation first * anchorEvaluation second +
      inner ℝ (embedding first) (embedding second) +
      (parameter - 1) * inner ℝ (embedding.adjoint (embedding first)) second = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  ring

theorem parameterAnchoredResolventBilinear_coercive_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) :
    IsCoercive (parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter) := by
  obtain ⟨coefficient, positive, lower⟩ := baseCoercive
  refine ⟨coefficient, positive, fun potential => (lower potential).trans ?_⟩
  rw [parameterAnchoredResolventBilinear_apply_completion20261011,
    anchoredResolventBilinear_apply_completion20261011]
  have squareNonnegative : 0 ≤ inner ℝ (embedding potential) (embedding potential) := by
    rw [real_inner_self_eq_norm_sq]
    positivity
  nlinarith

def normalizedAnchoredResolventSolutionCompletion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : Energy) : Energy :=
  (parameterAnchoredResolventBilinear_coercive_completion20261011 embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne).continuousLinearEquivOfBilin.symm
      (parameter • embedding.adjoint (embedding forcing))

theorem normalizedAnchoredResolventSolution_variational_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing test : Energy) :
    parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter
      (normalizedAnchoredResolventSolutionCompletion20261011 embedding anchorEvaluation
        baseCoercive parameter parameterAtLeastOne forcing) test =
      parameter * inner ℝ (embedding forcing) (embedding test) := by
  let coercive := parameterAnchoredResolventBilinear_coercive_completion20261011
    embedding anchorEvaluation baseCoercive parameter parameterAtLeastOne
  change parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter
    (coercive.continuousLinearEquivOfBilin.symm (parameter • embedding.adjoint (embedding forcing))) test = _
  rw [← coercive.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply,
    inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
  simp

def anchoredEnergySquareCompletion20261011
    (anchorEvaluation : StrongDual ℝ Energy) (potential : Energy) : ℝ :=
  ‖potential‖ ^ 2 - anchorEvaluation potential ^ 2

/-- The approximation estimates follow from testing the actual
variational equation against the solution minus the finite-energy
forcing. No semigroup continuity is assumed. -/
theorem normalizedAnchoredResolventSolution_energy_identity_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : Energy) :
    let solution := normalizedAnchoredResolventSolutionCompletion20261011 embedding anchorEvaluation
      baseCoercive parameter parameterAtLeastOne forcing
    anchoredEnergySquareCompletion20261011 anchorEvaluation solution +
      anchoredEnergySquareCompletion20261011 anchorEvaluation (solution - forcing) +
      2 * parameter * ‖embedding (solution - forcing)‖ ^ 2 =
        anchoredEnergySquareCompletion20261011 anchorEvaluation forcing := by
  intro solution
  have equation := normalizedAnchoredResolventSolution_variational_completion20261011 embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne forcing (solution - forcing)
  change parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter
    solution (solution - forcing) = _ at equation
  rw [parameterAnchoredResolventBilinear_apply_completion20261011, inner_sub_right,
    map_sub, map_sub, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm (embedding forcing) (embedding solution)] at equation
  unfold anchoredEnergySquareCompletion20261011
  rw [norm_sub_sq_real, map_sub, map_sub, norm_sub_sq_real]
  rw [real_inner_comm (embedding solution) (embedding forcing)] at equation
  nlinarith [equation]

theorem normalizedAnchoredResolventSolution_approximation_bounds_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (energyNonnegative : ∀ potential, 0 ≤ anchoredEnergySquareCompletion20261011 anchorEvaluation potential)
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : Energy) :
    let solution := normalizedAnchoredResolventSolutionCompletion20261011 embedding anchorEvaluation
      baseCoercive parameter parameterAtLeastOne forcing
    anchoredEnergySquareCompletion20261011 anchorEvaluation solution ≤
      anchoredEnergySquareCompletion20261011 anchorEvaluation forcing ∧
    ‖embedding (solution - forcing)‖ ^ 2 ≤
      anchoredEnergySquareCompletion20261011 anchorEvaluation forcing / parameter := by
  intro solution
  have identity := normalizedAnchoredResolventSolution_energy_identity_completion20261011 embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne forcing
  change anchoredEnergySquareCompletion20261011 anchorEvaluation solution +
    anchoredEnergySquareCompletion20261011 anchorEvaluation (solution - forcing) +
    2 * parameter * ‖embedding (solution - forcing)‖ ^ 2 = _ at identity
  have parameterPositive : 0 < parameter := lt_of_lt_of_le zero_lt_one parameterAtLeastOne
  constructor
  · nlinarith [energyNonnegative (solution - forcing), sq_nonneg ‖embedding (solution - forcing)‖]
  · apply (le_div_iff₀ parameterPositive).mpr
    nlinarith [energyNonnegative solution, energyNonnegative (solution - forcing),
      sq_nonneg ‖embedding (solution - forcing)‖]

theorem normalizedAnchoredResolventSolution_L2_bound_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (energyNonnegative : ∀ potential, 0 ≤ anchoredEnergySquareCompletion20261011 anchorEvaluation potential)
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : Energy) :
    ‖embedding (normalizedAnchoredResolventSolutionCompletion20261011 embedding anchorEvaluation
      baseCoercive parameter parameterAtLeastOne forcing)‖ ≤ ‖embedding forcing‖ := by
  let solution := normalizedAnchoredResolventSolutionCompletion20261011 embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne forcing
  have equation := normalizedAnchoredResolventSolution_variational_completion20261011 embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne forcing solution
  change parameterAnchoredResolventBilinearCompletion20261011 embedding anchorEvaluation parameter solution solution = _ at equation
  rw [parameterAnchoredResolventBilinear_apply_completion20261011,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at equation
  have positive : 0 < parameter := zero_lt_one.trans_le parameterAtLeastOne
  have upper := mul_le_mul_of_nonneg_left (real_inner_le_norm (embedding forcing) (embedding solution)) positive.le
  have energyPositive := energyNonnegative solution
  unfold anchoredEnergySquareCompletion20261011 at energyPositive
  have cancellation : ‖embedding solution‖ ^ 2 ≤ ‖embedding forcing‖ * ‖embedding solution‖ := by
    apply (mul_le_mul_iff_right₀ positive).mp
    nlinarith
  change ‖embedding solution‖ ≤ _
  nlinarith [norm_nonneg (embedding solution), norm_nonneg (embedding forcing)]

theorem normalizedAnchoredResolventSolution_L2_tendsto_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (energyNonnegative : ∀ potential, 0 ≤ anchoredEnergySquareCompletion20261011 anchorEvaluation potential)
    (parameters : ℕ → ℝ) (parametersAtLeastOne : ∀ index, 1 ≤ parameters index)
    (parametersDiverge : Tendsto parameters atTop atTop) (forcing : Energy) :
    Tendsto (fun index => embedding (normalizedAnchoredResolventSolutionCompletion20261011 embedding anchorEvaluation
      baseCoercive (parameters index) (parametersAtLeastOne index) forcing)) atTop (𝓝 (embedding forcing)) := by
  have squareLimit : Tendsto (fun index => ‖embedding
      (normalizedAnchoredResolventSolutionCompletion20261011 embedding anchorEvaluation
        baseCoercive (parameters index) (parametersAtLeastOne index) forcing - forcing)‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun index =>
      (normalizedAnchoredResolventSolution_approximation_bounds_completion20261011 embedding anchorEvaluation
        baseCoercive energyNonnegative (parameters index) (parametersAtLeastOne index) forcing).2)
      (tendsto_const_nhds.div_atTop parametersDiverge)
  have normLimit : Tendsto (fun index => ‖embedding
      (normalizedAnchoredResolventSolutionCompletion20261011 embedding anchorEvaluation
        baseCoercive (parameters index) (parametersAtLeastOne index) forcing - forcing)‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using squareLimit.sqrt
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [map_sub] using normLimit

theorem normalizedAnchoredResolventSolution_domain_bound_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (energyNonnegative : ∀ potential, 0 ≤ anchoredEnergySquareCompletion20261011 anchorEvaluation potential)
    (forcing : Energy) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ‖forcing‖ ≤ bound ∧
      ∀ (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter),
        ‖normalizedAnchoredResolventSolutionCompletion20261011 embedding anchorEvaluation
          baseCoercive parameter parameterAtLeastOne forcing‖ ≤ bound := by
  have coerciveCopy := baseCoercive
  obtain ⟨coefficient, coefficientPositive, coefficientBound⟩ := coerciveCopy
  let bound := Real.sqrt ((anchoredEnergySquareCompletion20261011 anchorEvaluation forcing +
    ‖embedding forcing‖ ^ 2) / coefficient) + ‖forcing‖
  refine ⟨bound, by dsimp [bound]; positivity, ?_, ?_⟩
  · dsimp [bound]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  intro parameter parameterAtLeastOne
  let solution := normalizedAnchoredResolventSolutionCompletion20261011 embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne forcing
  have energyBound := (normalizedAnchoredResolventSolution_approximation_bounds_completion20261011 embedding
    anchorEvaluation baseCoercive energyNonnegative parameter parameterAtLeastOne forcing).1
  have massBound := normalizedAnchoredResolventSolution_L2_bound_completion20261011 embedding anchorEvaluation
    baseCoercive energyNonnegative parameter parameterAtLeastOne forcing
  have lower := coefficientBound solution
  rw [anchoredResolventBilinear_self_completion20261011] at lower
  have squareBound : ‖solution‖ ^ 2 ≤
      (anchoredEnergySquareCompletion20261011 anchorEvaluation forcing + ‖embedding forcing‖ ^ 2) / coefficient := by
    apply (le_div_iff₀ coefficientPositive).mpr
    change ‖solution‖ ^ 2 - anchorEvaluation solution ^ 2 ≤ _ at energyBound
    change ‖embedding solution‖ ≤ _ at massBound
    have massSquareBound := (sq_le_sq₀ (norm_nonneg (embedding solution)) (norm_nonneg (embedding forcing))).mpr massBound
    nlinarith
  have boundNonnegative : 0 ≤
      (anchoredEnergySquareCompletion20261011 anchorEvaluation forcing + ‖embedding forcing‖ ^ 2) / coefficient :=
    div_nonneg (add_nonneg (energyNonnegative forcing) (sq_nonneg _)) coefficientPositive.le
  have normBound : ‖solution‖ ≤ Real.sqrt
      ((anchoredEnergySquareCompletion20261011 anchorEvaluation forcing + ‖embedding forcing‖ ^ 2) / coefficient) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt boundNonnegative]
    exact squareBound
  exact normBound.trans (le_add_of_nonneg_right (norm_nonneg _))

end
end IGSIII34.Diffusion
