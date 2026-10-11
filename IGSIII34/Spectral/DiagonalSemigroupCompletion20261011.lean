import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! The contraction semigroup constructed from the genuine L2 eigenbasis.
Pointwise coefficient convergence is upgraded to strong continuity using
finite Hilbert projections and a uniform operator bound. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace Filter
open scoped Topology NNReal

def boundedDiagonalL2ValueCompletion20261011 {Index : Type*}
    (coefficient : Index → ℝ) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ index, |coefficient index| ≤ bound)
    (value : lp (fun _ : Index => ℝ) 2) : lp (fun _ : Index => ℝ) 2 :=
  ⟨fun index => coefficient index * value index,
    (value.property.const_smul bound).mono' (fun index => by
      change ‖coefficient index * value index‖ ≤ ‖bound * value index‖
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg boundNonnegative]
      exact mul_le_mul_of_nonneg_right (bounded index) (abs_nonneg _))⟩

theorem boundedDiagonalL2Value_norm_le_completion20261011 {Index : Type*}
    (coefficient : Index → ℝ) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ index, |coefficient index| ≤ bound)
    (value : lp (fun _ : Index => ℝ) 2) :
    ‖boundedDiagonalL2ValueCompletion20261011 coefficient bound boundNonnegative bounded value‖ ≤ bound * ‖value‖ := by
  have comparison : ‖boundedDiagonalL2ValueCompletion20261011 coefficient bound boundNonnegative bounded value‖ ≤
      ‖bound • value‖ := by
    apply lp.norm_mono (by norm_num)
    intro index
    change ‖coefficient index * value index‖ ≤ ‖bound * value index‖
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg boundNonnegative]
    exact mul_le_mul_of_nonneg_right (bounded index) (abs_nonneg _)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg boundNonnegative] using comparison

def boundedDiagonalL2Completion20261011 {Index : Type*}
    (coefficient : Index → ℝ) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (bounded : ∀ index, |coefficient index| ≤ bound) :
    lp (fun _ : Index => ℝ) 2 →L[ℝ] lp (fun _ : Index => ℝ) 2 :=
  (show lp (fun _ : Index => ℝ) 2 →ₗ[ℝ] lp (fun _ : Index => ℝ) 2 from
    { toFun := boundedDiagonalL2ValueCompletion20261011 coefficient bound boundNonnegative bounded
      map_add' := by
        intro first second
        ext index
        change coefficient index * (first index + second index) = coefficient index * first index + coefficient index * second index
        ring
      map_smul' := by
        intro scalar value
        ext index
        change coefficient index * (scalar * value index) = scalar * (coefficient index * value index)
        ring }).mkContinuous bound
          (boundedDiagonalL2Value_norm_le_completion20261011 coefficient bound boundNonnegative bounded)

variable {Hilbert Index : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  [CompleteSpace Hilbert]

def spectralL2SemigroupCompletion20261011
    (basis : HilbertBasis Index ℝ Hilbert) (eigenvalues : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ eigenvalues index) (time : ℝ≥0) : Hilbert →L[ℝ] Hilbert :=
  basis.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((boundedDiagonalL2Completion20261011 (fun index => Real.exp (-(time : ℝ) * eigenvalues index)) 1 zero_le_one
      (fun index => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr time.property) (nonnegative index)))).comp
      basis.repr.toContinuousLinearEquiv.toContinuousLinearMap)

theorem spectralL2Semigroup_repr_completion20261011
    (basis : HilbertBasis Index ℝ Hilbert) (eigenvalues : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ eigenvalues index) (time : ℝ≥0) (value : Hilbert) (index : Index) :
    basis.repr (spectralL2SemigroupCompletion20261011 basis eigenvalues nonnegative time value) index =
      Real.exp (-(time : ℝ) * eigenvalues index) * basis.repr value index := by
  change basis.repr (basis.repr.symm _) index = _
  rw [basis.repr.apply_symm_apply]
  rfl

theorem spectralL2Semigroup_norm_le_completion20261011
    (basis : HilbertBasis Index ℝ Hilbert) (eigenvalues : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ eigenvalues index) (time : ℝ≥0) (value : Hilbert) :
    ‖spectralL2SemigroupCompletion20261011 basis eigenvalues nonnegative time value‖ ≤ ‖value‖ := by
  change ‖basis.repr.symm _‖ ≤ ‖value‖
  rw [basis.repr.symm.norm_map]
  change ‖boundedDiagonalL2ValueCompletion20261011
    (fun index => Real.exp (-(time : ℝ) * eigenvalues index)) 1 zero_le_one
    (fun index => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr time.property) (nonnegative index)))
    (basis.repr value)‖ ≤ ‖value‖
  have bound := boundedDiagonalL2Value_norm_le_completion20261011
    (fun index => Real.exp (-(time : ℝ) * eigenvalues index)) 1 zero_le_one
    (fun index => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr time.property) (nonnegative index)))
    (basis.repr value)
  simpa only [one_mul, basis.repr.norm_map] using bound

theorem spectralL2Semigroup_zero_completion20261011
    (basis : HilbertBasis Index ℝ Hilbert) (eigenvalues : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ eigenvalues index) (value : Hilbert) :
    spectralL2SemigroupCompletion20261011 basis eigenvalues nonnegative 0 value = value := by
  apply basis.repr.injective
  ext index
  rw [spectralL2Semigroup_repr_completion20261011]
  simp

theorem spectralL2Semigroup_add_completion20261011
    (basis : HilbertBasis Index ℝ Hilbert) (eigenvalues : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ eigenvalues index) (first second : ℝ≥0) (value : Hilbert) :
    spectralL2SemigroupCompletion20261011 basis eigenvalues nonnegative first
      (spectralL2SemigroupCompletion20261011 basis eigenvalues nonnegative second value) =
        spectralL2SemigroupCompletion20261011 basis eigenvalues nonnegative (first + second) value := by
  apply basis.repr.injective
  ext index
  rw [spectralL2Semigroup_repr_completion20261011, spectralL2Semigroup_repr_completion20261011,
    spectralL2Semigroup_repr_completion20261011, ← mul_assoc, ← Real.exp_add]
  congr 2
  push_cast
  ring

theorem spectralL2Semigroup_basis_completion20261011
    (basis : HilbertBasis Index ℝ Hilbert) (eigenvalues : Index → ℝ)
    (nonnegative : ∀ index, 0 ≤ eigenvalues index) (time : ℝ≥0) (index : Index) :
    spectralL2SemigroupCompletion20261011 basis eigenvalues nonnegative time (basis index) =
      Real.exp (-(time : ℝ) * eigenvalues index) • basis index := by
  classical
  apply basis.repr.injective
  ext other
  rw [spectralL2Semigroup_repr_completion20261011, map_smul, basis.repr_self]
  simp only [lp.single_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases same : other = index
  · subst other
    simp
  · simp [same, Ne.symm same]

end
end IGSIII34.Spectral

