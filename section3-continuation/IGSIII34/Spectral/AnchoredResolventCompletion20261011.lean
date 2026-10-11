import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-! The Lax-Milgram resolvent of the energy plus L² form represented in an
anchored Hilbert norm. Compactness of the embedding is used to prove
compactness of the resulting resolvent, rather than assume it. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace
open scoped Topology

variable {Energy L2 : Type*}
  [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
  [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]

def anchoredResolventOperatorCompletion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy) : Energy →L[ℝ] Energy :=
  ContinuousLinearMap.id ℝ Energy -
    anchorEvaluation.smulRight ((toDual ℝ Energy).symm anchorEvaluation) +
      embedding.adjoint.comp embedding

def anchoredResolventBilinearCompletion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy) :
    Energy →L[ℝ] Energy →L[ℝ] ℝ :=
  (innerSL ℝ).comp (anchoredResolventOperatorCompletion20261011 embedding anchorEvaluation)

theorem anchoredResolventBilinear_apply_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (first second : Energy) :
    anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation first second =
      inner ℝ first second - anchorEvaluation first * anchorEvaluation second +
        inner ℝ (embedding first) (embedding second) := by
  simp [anchoredResolventBilinearCompletion20261011, anchoredResolventOperatorCompletion20261011,
    inner_add_left, inner_sub_left, inner_smul_left, toDual_symm_apply,
    ContinuousLinearMap.adjoint_inner_left]
  rfl

theorem anchoredResolventBilinear_self_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (function : Energy) :
    anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation function function =
      ‖function‖ ^ 2 - anchorEvaluation function ^ 2 + ‖embedding function‖ ^ 2 := by
  rw [anchoredResolventBilinear_apply_completion20261011,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  ring

theorem anchoredResolventBilinear_symmetric_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (first second : Energy) :
    anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation first second =
      anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation second first := by
  rw [anchoredResolventBilinear_apply_completion20261011,
    anchoredResolventBilinear_apply_completion20261011, real_inner_comm first second,
    real_inner_comm (embedding first) (embedding second), mul_comm (anchorEvaluation first)]

theorem anchoredResolventBilinear_coercive_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (coefficient : ℝ) (positive : 0 < coefficient)
    (normComparison : ∀ function : Energy, ‖function‖ ^ 2 ≤ coefficient *
      (‖function‖ ^ 2 - anchorEvaluation function ^ 2 + ‖embedding function‖ ^ 2)) :
    IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation) := by
  refine ⟨coefficient⁻¹, inv_pos.mpr positive, ?_⟩
  intro function
  rw [anchoredResolventBilinear_self_completion20261011]
  have comparison : ‖function‖ ^ 2 / coefficient ≤
      ‖function‖ ^ 2 - anchorEvaluation function ^ 2 + ‖embedding function‖ ^ 2 := by
    apply (div_le_iff₀ positive).mpr
    nlinarith [normComparison function]
  simpa only [div_eq_mul_inv, pow_two, mul_assoc, mul_comm, mul_left_comm] using comparison

def anchoredL2ResolventCompletion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (coercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation)) :
    L2 →L[ℝ] L2 :=
  embedding.comp (coercive.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp embedding.adjoint)

theorem anchoredL2Resolvent_compact_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (coercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (compact : IsCompactOperator embedding) :
    IsCompactOperator (anchoredL2ResolventCompletion20261011 embedding anchorEvaluation coercive) :=
  compact.comp_clm (coercive.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp embedding.adjoint)

theorem anchoredL2Resolvent_variational_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (coercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (forcing : L2) (test : Energy) :
    anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation
      (coercive.continuousLinearEquivOfBilin.symm (embedding.adjoint forcing)) test =
        inner ℝ forcing (embedding test) := by
  rw [← coercive.continuousLinearEquivOfBilin_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.adjoint_inner_left]

theorem anchoredL2Resolvent_symmetric_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (coercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation)) :
    (anchoredL2ResolventCompletion20261011 embedding anchorEvaluation coercive).toLinearMap.IsSymmetric := by
  intro first second
  let firstSolution := coercive.continuousLinearEquivOfBilin.symm (embedding.adjoint first)
  let secondSolution := coercive.continuousLinearEquivOfBilin.symm (embedding.adjoint second)
  have firstIdentity := anchoredL2Resolvent_variational_completion20261011 embedding anchorEvaluation
    coercive first secondSolution
  have secondIdentity := anchoredL2Resolvent_variational_completion20261011 embedding anchorEvaluation
    coercive second firstSolution
  have symmetry := anchoredResolventBilinear_symmetric_completion20261011 embedding anchorEvaluation
    firstSolution secondSolution
  change inner ℝ (embedding firstSolution) second = inner ℝ first (embedding secondSolution)
  exact (real_inner_comm second (embedding firstSolution)).trans
    (secondIdentity.symm.trans (symmetry.symm.trans firstIdentity))

theorem anchoredL2Resolvent_nonnegative_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (coercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (forcing : L2) :
    0 ≤ inner ℝ (anchoredL2ResolventCompletion20261011 embedding anchorEvaluation coercive forcing) forcing := by
  let solution := coercive.continuousLinearEquivOfBilin.symm (embedding.adjoint forcing)
  have identity := anchoredL2Resolvent_variational_completion20261011 embedding anchorEvaluation
    coercive forcing solution
  obtain ⟨coefficient, positive, bounded⟩ := coercive
  have below := bounded solution
  change 0 ≤ inner ℝ (embedding solution) forcing
  rw [real_inner_comm]
  exact (by positivity : 0 ≤ coefficient * ‖solution‖ * ‖solution‖).trans (below.trans_eq identity)

theorem anchoredL2Resolvent_kernel_zero_completion20261011
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (coercive : IsCoercive (anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation))
    (dense : DenseRange embedding) (forcing : L2)
    (zero : anchoredL2ResolventCompletion20261011 embedding anchorEvaluation coercive forcing = 0) :
    forcing = 0 := by
  let solution := coercive.continuousLinearEquivOfBilin.symm (embedding.adjoint forcing)
  have imageZero : embedding solution = 0 := zero
  have identity := anchoredL2Resolvent_variational_completion20261011 embedding anchorEvaluation
    coercive forcing solution
  have formZero : anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation solution solution = 0 := by
    simpa only [imageZero, inner_zero_right] using identity
  obtain ⟨coefficient, positive, bounded⟩ := (show IsCoercive _ from coercive)
  have normZero : ‖solution‖ = 0 := by
    have below := bounded solution
    rw [formZero] at below
    by_contra nonzero
    have normPositive := lt_of_le_of_ne (norm_nonneg solution) (Ne.symm nonzero)
    exact (not_le_of_gt (mul_pos (mul_pos positive normPositive) normPositive)) below
  have solutionZero : solution = 0 := norm_eq_zero.mp normZero
  have vanishing (test : Energy) : inner ℝ forcing (embedding test) = 0 := by
    have equation := anchoredL2Resolvent_variational_completion20261011 embedding anchorEvaluation
      coercive forcing test
    change anchoredResolventBilinearCompletion20261011 embedding anchorEvaluation solution test = _ at equation
    rw [solutionZero] at equation
    simpa only [map_zero, ContinuousLinearMap.zero_apply] using equation.symm
  have all : (fun vector : L2 => inner ℝ forcing vector) = (fun _ => (0 : ℝ)) :=
    dense.equalizer (continuous_const.inner continuous_id) continuous_const (funext vanishing)
  have square := congrFun all forcing
  rw [real_inner_self_eq_norm_sq] at square
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg forcing])

end
end IGSIII34.Spectral
