import IGSIII34.Spectral.AnchoredResolventCompletion
import IGSIII34.Diffusion.CompactL2UniformCompletion

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace IGSIII34.Diffusion
noncomputable section
open IGSIII34.Spectral InnerProductSpace MeasureTheory Filter
open scoped Topology

variable {Energy L2 : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]

def parameterAnchoredResolventBilinearCompletion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (parameter : ℝ) : Energy →L[ℝ] Energy →L[ℝ] ℝ :=
  anchoredResolventBilinearCompletion embedding anchorEvaluation +
    (parameter - 1) • ((innerSL ℝ).comp (embedding.adjoint.comp embedding))

theorem parameterAnchoredResolventBilinear_apply_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (parameter : ℝ) (first second : Energy) :
    parameterAnchoredResolventBilinearCompletion embedding anchorEvaluation parameter first second =
      inner ℝ first second - anchorEvaluation first * anchorEvaluation second +
        parameter * inner ℝ (embedding first) (embedding second) := by
  simp only [parameterAnchoredResolventBilinearCompletion, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul]
  rw [anchoredResolventBilinear_apply_completion]
  change inner ℝ first second - anchorEvaluation first * anchorEvaluation second +
      inner ℝ (embedding first) (embedding second) +
      (parameter - 1) * inner ℝ (embedding.adjoint (embedding first)) second = _
  rw [ContinuousLinearMap.adjoint_inner_left]
  ring

theorem parameterAnchoredResolventBilinear_coercive_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) :
    IsCoercive (parameterAnchoredResolventBilinearCompletion embedding anchorEvaluation parameter) := by
  obtain ⟨coefficient, positive, lower⟩ := baseCoercive
  refine ⟨coefficient, positive, fun potential => (lower potential).trans ?_⟩
  rw [parameterAnchoredResolventBilinear_apply_completion,
    anchoredResolventBilinear_apply_completion]
  have squareNonnegative : 0 ≤ inner ℝ (embedding potential) (embedding potential) := by
    rw [real_inner_self_eq_norm_sq]
    positivity
  nlinarith

def normalizedAnchoredResolventSolutionCompletion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : Energy) : Energy :=
  (parameterAnchoredResolventBilinear_coercive_completion embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne).continuousLinearEquivOfBilin.symm
      (parameter • embedding.adjoint (embedding forcing))

theorem normalizedAnchoredResolventSolution_variational_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing test : Energy) :
    parameterAnchoredResolventBilinearCompletion embedding anchorEvaluation parameter
      (normalizedAnchoredResolventSolutionCompletion embedding anchorEvaluation
        baseCoercive parameter parameterAtLeastOne forcing) test =
      parameter * inner ℝ (embedding forcing) (embedding test) := by
  let coercive := parameterAnchoredResolventBilinear_coercive_completion
    embedding anchorEvaluation baseCoercive parameter parameterAtLeastOne
  change parameterAnchoredResolventBilinearCompletion embedding anchorEvaluation parameter
    (coercive.continuousLinearEquivOfBilin.symm (parameter • embedding.adjoint (embedding forcing))) test = _
  rw [← coercive.continuousLinearEquivOfBilin_apply, ContinuousLinearEquiv.apply_symm_apply,
    inner_smul_left, ContinuousLinearMap.adjoint_inner_left]
  simp

def anchoredEnergySquareCompletion
    (anchorEvaluation : StrongDual ℝ Energy) (potential : Energy) : ℝ :=
  ‖potential‖ ^ 2 - anchorEvaluation potential ^ 2

/-- The approximation estimates follow from testing the actual
variational equation against the solution minus the finite-energy
forcing. No semigroup continuity is assumed. -/
theorem normalizedAnchoredResolventSolution_energy_identity_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : Energy) :
    let solution := normalizedAnchoredResolventSolutionCompletion embedding anchorEvaluation
      baseCoercive parameter parameterAtLeastOne forcing
    anchoredEnergySquareCompletion anchorEvaluation solution +
      anchoredEnergySquareCompletion anchorEvaluation (solution - forcing) +
      2 * parameter * ‖embedding (solution - forcing)‖ ^ 2 =
        anchoredEnergySquareCompletion anchorEvaluation forcing := by
  intro solution
  have equation := normalizedAnchoredResolventSolution_variational_completion embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne forcing (solution - forcing)
  change parameterAnchoredResolventBilinearCompletion embedding anchorEvaluation parameter
    solution (solution - forcing) = _ at equation
  rw [parameterAnchoredResolventBilinear_apply_completion, inner_sub_right,
    map_sub, map_sub, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm (embedding forcing) (embedding solution)] at equation
  unfold anchoredEnergySquareCompletion
  rw [norm_sub_sq_real, map_sub, map_sub, norm_sub_sq_real]
  rw [real_inner_comm (embedding solution) (embedding forcing)] at equation
  nlinarith [equation]

theorem normalizedAnchoredResolventSolution_approximation_bounds_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (energyNonnegative : ∀ potential, 0 ≤ anchoredEnergySquareCompletion anchorEvaluation potential)
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : Energy) :
    let solution := normalizedAnchoredResolventSolutionCompletion embedding anchorEvaluation
      baseCoercive parameter parameterAtLeastOne forcing
    anchoredEnergySquareCompletion anchorEvaluation solution ≤
      anchoredEnergySquareCompletion anchorEvaluation forcing ∧
    ‖embedding (solution - forcing)‖ ^ 2 ≤
      anchoredEnergySquareCompletion anchorEvaluation forcing / parameter := by
  intro solution
  have identity := normalizedAnchoredResolventSolution_energy_identity_completion embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne forcing
  change anchoredEnergySquareCompletion anchorEvaluation solution +
    anchoredEnergySquareCompletion anchorEvaluation (solution - forcing) +
    2 * parameter * ‖embedding (solution - forcing)‖ ^ 2 = _ at identity
  have parameterPositive : 0 < parameter := lt_of_lt_of_le zero_lt_one parameterAtLeastOne
  constructor
  · nlinarith [energyNonnegative (solution - forcing), sq_nonneg ‖embedding (solution - forcing)‖]
  · apply (le_div_iff₀ parameterPositive).mpr
    nlinarith [energyNonnegative solution, energyNonnegative (solution - forcing),
      sq_nonneg ‖embedding (solution - forcing)‖]

theorem normalizedAnchoredResolventSolution_L2_bound_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (energyNonnegative : ∀ potential, 0 ≤ anchoredEnergySquareCompletion anchorEvaluation potential)
    (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter) (forcing : Energy) :
    ‖embedding (normalizedAnchoredResolventSolutionCompletion embedding anchorEvaluation
      baseCoercive parameter parameterAtLeastOne forcing)‖ ≤ ‖embedding forcing‖ := by
  let solution := normalizedAnchoredResolventSolutionCompletion embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne forcing
  have equation := normalizedAnchoredResolventSolution_variational_completion embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne forcing solution
  change parameterAnchoredResolventBilinearCompletion embedding anchorEvaluation parameter solution solution = _ at equation
  rw [parameterAnchoredResolventBilinear_apply_completion,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at equation
  have positive : 0 < parameter := zero_lt_one.trans_le parameterAtLeastOne
  have upper := mul_le_mul_of_nonneg_left (real_inner_le_norm (embedding forcing) (embedding solution)) positive.le
  have energyPositive := energyNonnegative solution
  unfold anchoredEnergySquareCompletion at energyPositive
  have cancellation : ‖embedding solution‖ ^ 2 ≤ ‖embedding forcing‖ * ‖embedding solution‖ := by
    apply (mul_le_mul_iff_right₀ positive).mp
    nlinarith
  change ‖embedding solution‖ ≤ _
  nlinarith [norm_nonneg (embedding solution), norm_nonneg (embedding forcing)]

theorem normalizedAnchoredResolventSolution_L2_tendsto_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (energyNonnegative : ∀ potential, 0 ≤ anchoredEnergySquareCompletion anchorEvaluation potential)
    (parameters : ℕ → ℝ) (parametersAtLeastOne : ∀ index, 1 ≤ parameters index)
    (parametersDiverge : Tendsto parameters atTop atTop) (forcing : Energy) :
    Tendsto (fun index => embedding (normalizedAnchoredResolventSolutionCompletion embedding anchorEvaluation
      baseCoercive (parameters index) (parametersAtLeastOne index) forcing)) atTop (𝓝 (embedding forcing)) := by
  have squareLimit : Tendsto (fun index => ‖embedding
      (normalizedAnchoredResolventSolutionCompletion embedding anchorEvaluation
        baseCoercive (parameters index) (parametersAtLeastOne index) forcing - forcing)‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) (fun index =>
      (normalizedAnchoredResolventSolution_approximation_bounds_completion embedding anchorEvaluation
        baseCoercive energyNonnegative (parameters index) (parametersAtLeastOne index) forcing).2)
      (tendsto_const_nhds.div_atTop parametersDiverge)
  have normLimit : Tendsto (fun index => ‖embedding
      (normalizedAnchoredResolventSolutionCompletion embedding anchorEvaluation
        baseCoercive (parameters index) (parametersAtLeastOne index) forcing - forcing)‖) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)] using squareLimit.sqrt
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [map_sub] using normLimit

theorem normalizedAnchoredResolventSolution_domain_bound_completion
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (baseCoercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (energyNonnegative : ∀ potential, 0 ≤ anchoredEnergySquareCompletion anchorEvaluation potential)
    (forcing : Energy) :
    ∃ bound : ℝ, 0 ≤ bound ∧ ‖forcing‖ ≤ bound ∧
      ∀ (parameter : ℝ) (parameterAtLeastOne : 1 ≤ parameter),
        ‖normalizedAnchoredResolventSolutionCompletion embedding anchorEvaluation
          baseCoercive parameter parameterAtLeastOne forcing‖ ≤ bound := by
  have coerciveCopy := baseCoercive
  obtain ⟨coefficient, coefficientPositive, coefficientBound⟩ := coerciveCopy
  let bound := Real.sqrt ((anchoredEnergySquareCompletion anchorEvaluation forcing +
    ‖embedding forcing‖ ^ 2) / coefficient) + ‖forcing‖
  refine ⟨bound, by dsimp [bound]; positivity, ?_, ?_⟩
  · dsimp [bound]
    exact le_add_of_nonneg_left (Real.sqrt_nonneg _)
  intro parameter parameterAtLeastOne
  let solution := normalizedAnchoredResolventSolutionCompletion embedding anchorEvaluation
    baseCoercive parameter parameterAtLeastOne forcing
  have energyBound := (normalizedAnchoredResolventSolution_approximation_bounds_completion embedding
    anchorEvaluation baseCoercive energyNonnegative parameter parameterAtLeastOne forcing).1
  have massBound := normalizedAnchoredResolventSolution_L2_bound_completion embedding anchorEvaluation
    baseCoercive energyNonnegative parameter parameterAtLeastOne forcing
  have lower := coefficientBound solution
  rw [anchoredResolventBilinear_self_completion] at lower
  have squareBound : ‖solution‖ ^ 2 ≤
      (anchoredEnergySquareCompletion anchorEvaluation forcing + ‖embedding forcing‖ ^ 2) / coefficient := by
    apply (le_div_iff₀ coefficientPositive).mpr
    change ‖solution‖ ^ 2 - anchorEvaluation solution ^ 2 ≤ _ at energyBound
    change ‖embedding solution‖ ≤ _ at massBound
    have massSquareBound := (sq_le_sq₀ (norm_nonneg (embedding solution)) (norm_nonneg (embedding forcing))).mpr massBound
    nlinarith
  have boundNonnegative : 0 ≤
      (anchoredEnergySquareCompletion anchorEvaluation forcing + ‖embedding forcing‖ ^ 2) / coefficient :=
    div_nonneg (add_nonneg (energyNonnegative forcing) (sq_nonneg _)) coefficientPositive.le
  have normBound : ‖solution‖ ≤ Real.sqrt
      ((anchoredEnergySquareCompletion anchorEvaluation forcing + ‖embedding forcing‖ ^ 2) / coefficient) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [Real.sq_sqrt boundNonnegative]
    exact squareBound
  exact normBound.trans (le_add_of_nonneg_right (norm_nonneg _))

end
end IGSIII34.Diffusion
