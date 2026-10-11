import IGSIII34.Spectral.AnchoredResolventCompletion20261011
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.UniformSpace.Equiv

/-! A symmetric coercive energy form defines its genuine Hilbert norm. Its
completeness is transported through the proved two-sided norm comparison.
This supplies the energy-plus-L2 space needed by spectral evaluation. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace
open scoped Topology

variable {Energy : Type*} [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy]
  [CompleteSpace Energy]
  (bilinear : Energy →L[ℝ] Energy →L[ℝ] ℝ)
  (symmetric : ∀ first second, bilinear first second = bilinear second first)
  (coercive : IsCoercive bilinear)

def coerciveFormHilbertCompletion20261011
    (bilinear : Energy →L[ℝ] Energy →L[ℝ] ℝ)
    (symmetric : ∀ first second, bilinear first second = bilinear second first)
    (coercive : IsCoercive bilinear) : Type _ := Energy

instance coerciveFormAddCommGroupCompletion20261011 :
    AddCommGroup (coerciveFormHilbertCompletion20261011 bilinear symmetric coercive) :=
  inferInstanceAs (AddCommGroup Energy)

instance coerciveFormModuleCompletion20261011 :
    Module ℝ (coerciveFormHilbertCompletion20261011 bilinear symmetric coercive) :=
  inferInstanceAs (Module ℝ Energy)

def coerciveFormForgetCompletion20261011
    (function : coerciveFormHilbertCompletion20261011 bilinear symmetric coercive) : Energy := function

@[reducible] def coerciveFormInnerCoreCompletion20261011 :
    InnerProductSpace.Core ℝ (coerciveFormHilbertCompletion20261011 bilinear symmetric coercive) where
  inner first second := bilinear first second
  conj_inner_symm first second := by
    change bilinear (second : Energy) (first : Energy) = bilinear first second
    exact symmetric second first
  re_inner_nonneg function := by
    obtain ⟨coefficient, positive, bound⟩ := (show IsCoercive _ from coercive)
    exact (mul_nonneg (mul_nonneg positive.le (norm_nonneg (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function)))
      (norm_nonneg (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function))).trans
        (bound (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function))
  add_left first second third := by
    change bilinear ((first : Energy) + second) third = _
    exact congrFun (congrArg DFunLike.coe (bilinear.map_add (first : Energy) second)) third
  smul_left first second scalar := by
    change bilinear (scalar • (first : Energy)) second = scalar * bilinear first second
    simpa only [map_smul, smul_apply, smul_eq_mul] using congrFun
      (congrArg DFunLike.coe (bilinear.map_smul scalar (first : Energy))) second
  definite function zero := by
    obtain ⟨coefficient, positive, bound⟩ := (show IsCoercive _ from coercive)
    have below := bound (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function)
    change bilinear (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function)
      (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function) = 0 at zero
    rw [zero] at below
    have normZero : ‖coerciveFormForgetCompletion20261011 bilinear symmetric coercive function‖ = 0 := by
      by_contra nonzero
      have normPositive := lt_of_le_of_ne (norm_nonneg (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function)) (Ne.symm nonzero)
      exact (not_le_of_gt (mul_pos (mul_pos positive normPositive) normPositive)) below
    exact norm_eq_zero.mp normZero

instance coerciveFormNormCompletion20261011 :
    NormedAddCommGroup (coerciveFormHilbertCompletion20261011 bilinear symmetric coercive) := by
  letI := coerciveFormInnerCoreCompletion20261011 bilinear symmetric coercive
  exact InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

instance coerciveFormInnerCompletion20261011 :
    InnerProductSpace ℝ (coerciveFormHilbertCompletion20261011 bilinear symmetric coercive) := by
  letI := coerciveFormInnerCoreCompletion20261011 bilinear symmetric coercive
  exact InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ
    (coerciveFormHilbertCompletion20261011 bilinear symmetric coercive))

theorem coerciveForm_inner_completion20261011
    (first second : coerciveFormHilbertCompletion20261011 bilinear symmetric coercive) :
    inner ℝ first second = bilinear
      (coerciveFormForgetCompletion20261011 bilinear symmetric coercive first)
      (coerciveFormForgetCompletion20261011 bilinear symmetric coercive second) := rfl

theorem coerciveForm_norm_square_completion20261011
    (function : coerciveFormHilbertCompletion20261011 bilinear symmetric coercive) :
    ‖function‖ ^ 2 = bilinear
      (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function)
      (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function) :=
  (real_inner_self_eq_norm_sq function).symm

theorem coerciveForm_old_norm_le_completion20261011 :
    ∃ coefficient > 0, ∀ function : coerciveFormHilbertCompletion20261011 bilinear symmetric coercive,
      ‖coerciveFormForgetCompletion20261011 bilinear symmetric coercive function‖ ≤ coefficient * ‖function‖ := by
  obtain ⟨coefficient, positive, bound⟩ := (show IsCoercive _ from coercive)
  refine ⟨(Real.sqrt coefficient)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr positive), ?_⟩
  intro function
  have below := bound (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function)
  rw [← coerciveForm_norm_square_completion20261011 bilinear symmetric coercive function] at below
  have multiplied : Real.sqrt coefficient * ‖coerciveFormForgetCompletion20261011 bilinear symmetric coercive function‖ ≤ ‖function‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow, Real.sq_sqrt positive.le]
    nlinarith [below]
  rw [mul_comm ((Real.sqrt coefficient)⁻¹)]
  exact (le_mul_inv_iff₀ (Real.sqrt_pos.mpr positive)).mpr (by simpa only [mul_comm] using multiplied)

theorem coerciveForm_new_norm_le_completion20261011
    (function : coerciveFormHilbertCompletion20261011 bilinear symmetric coercive) :
    ‖function‖ ≤ Real.sqrt ‖bilinear‖ * ‖coerciveFormForgetCompletion20261011 bilinear symmetric coercive function‖ := by
  have bound := bilinear.le_opNorm₂
    (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function)
    (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function)
  have nonnegative : 0 ≤ bilinear
      (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function)
      (coerciveFormForgetCompletion20261011 bilinear symmetric coercive function) := by
    rw [← coerciveForm_norm_square_completion20261011 bilinear symmetric coercive function]
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg nonnegative,
    ← coerciveForm_norm_square_completion20261011 bilinear symmetric coercive function] at bound
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (norm_nonneg bilinear)]
  nlinarith [bound]

def coerciveFormEquivCompletion20261011 :
    coerciveFormHilbertCompletion20261011 bilinear symmetric coercive ≃L[ℝ] Energy := by
  let coefficient := Classical.choose (coerciveForm_old_norm_le_completion20261011 bilinear symmetric coercive)
  have bound := (Classical.choose_spec (coerciveForm_old_norm_le_completion20261011 bilinear symmetric coercive)).2
  let forward : coerciveFormHilbertCompletion20261011 bilinear symmetric coercive →ₗ[ℝ] Energy :=
    { toFun := coerciveFormForgetCompletion20261011 bilinear symmetric coercive
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let backward : Energy →ₗ[ℝ] coerciveFormHilbertCompletion20261011 bilinear symmetric coercive :=
    { toFun := fun function => function
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact
    { forward with
      invFun := backward
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := (forward.mkContinuous coefficient bound).continuous
      continuous_invFun := (backward.mkContinuous (Real.sqrt ‖bilinear‖) (fun function =>
        coerciveForm_new_norm_le_completion20261011 bilinear symmetric coercive function)).continuous }

instance coerciveFormCompleteCompletion20261011 :
    CompleteSpace (coerciveFormHilbertCompletion20261011 bilinear symmetric coercive) := by
  let equivalence := coerciveFormEquivCompletion20261011 bilinear symmetric coercive
  let uniform : coerciveFormHilbertCompletion20261011 bilinear symmetric coercive ≃ᵤ Energy :=
    { equivalence.toEquiv with
      uniformContinuous_toFun := equivalence.toContinuousLinearMap.uniformContinuous
      uniformContinuous_invFun := equivalence.symm.toContinuousLinearMap.uniformContinuous }
  exact uniform.completeSpace_iff.mpr inferInstance

end
end IGSIII34.Spectral
