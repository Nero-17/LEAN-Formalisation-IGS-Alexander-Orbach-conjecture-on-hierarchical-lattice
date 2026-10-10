import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Riesz representation proves the variational evaluation identity and
the bounded weighted spectral-evaluation sums used by the heat construction.
The actual form Hilbert space must still be supplied by the model construction.
-/
set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace
open scoped Topology

variable {Hilbert : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  [CompleteSpace Hilbert]

theorem evaluation_quotient_le_norm_square (evaluation : StrongDual ℝ Hilbert) (function : Hilbert) :
    evaluation function ^ 2 / ‖function‖ ^ 2 ≤ ‖evaluation‖ ^ 2 := by
  by_cases zero : ‖function‖ = 0
  · simp [zero]
  have bound := evaluation.le_opNorm function
  rw [Real.norm_eq_abs] at bound
  have squared : evaluation function ^ 2 ≤ ‖evaluation‖ ^ 2 * ‖function‖ ^ 2 := by
    nlinarith [sq_abs (evaluation function), abs_nonneg (evaluation function),
      norm_nonneg evaluation, norm_nonneg function]
  exact (div_le_iff₀ (sq_pos_of_ne_zero zero)).mpr squared

theorem evaluation_quotient_attains_norm_square (evaluation : StrongDual ℝ Hilbert) :
    evaluation ((toDual ℝ Hilbert).symm evaluation) ^ 2 /
      ‖(toDual ℝ Hilbert).symm evaluation‖ ^ 2 = ‖evaluation‖ ^ 2 := by
  rw [← toDual_symm_apply, real_inner_self_eq_norm_sq, (toDual ℝ Hilbert).symm.norm_map]
  by_cases zero : ‖evaluation‖ = 0
  · simp [zero]
  · field_simp

theorem evaluation_variational_identity (evaluation : StrongDual ℝ Hilbert) :
    sSup (Set.range (fun function : Hilbert => evaluation function ^ 2 / ‖function‖ ^ 2)) =
      ‖evaluation‖ ^ 2 := by
  have upper : BddAbove (Set.range (fun function : Hilbert =>
      evaluation function ^ 2 / ‖function‖ ^ 2)) := by
    refine ⟨‖evaluation‖ ^ 2, ?_⟩
    rintro value ⟨function, rfl⟩
    exact evaluation_quotient_le_norm_square evaluation function
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro value ⟨function, rfl⟩
    exact evaluation_quotient_le_norm_square evaluation function
  · rw [← evaluation_quotient_attains_norm_square evaluation]
    exact le_csSup upper (Set.mem_range_self _)

theorem finite_orthonormal_evaluation_bound {Index : Type*}
    (vectors : Index → Hilbert) (orthonormal : Orthonormal ℝ vectors)
    (evaluation : StrongDual ℝ Hilbert) (indices : Finset Index) :
    ∑ index ∈ indices, evaluation (vectors index) ^ 2 ≤ ‖evaluation‖ ^ 2 := by
  have bound := orthonormal.sum_inner_products_le ((toDual ℝ Hilbert).symm evaluation) (s := indices)
  have coefficients : ∀ index, inner ℝ (vectors index) ((toDual ℝ Hilbert).symm evaluation) =
      evaluation (vectors index) := fun index => (real_inner_comm _ _).trans toDual_symm_apply
  simpa only [coefficients, Real.norm_eq_abs, sq_abs,
    (toDual ℝ Hilbert).symm.norm_map] using bound

theorem hilbert_basis_evaluation_parseval {Index : Type*}
    (basis : HilbertBasis Index ℝ Hilbert) (evaluation : StrongDual ℝ Hilbert) :
    HasSum (fun index => evaluation (basis index) ^ 2) (‖evaluation‖ ^ 2) := by
  have identity := basis.hasSum_inner_mul_inner ((toDual ℝ Hilbert).symm evaluation)
    ((toDual ℝ Hilbert).symm evaluation)
  rw [real_inner_self_eq_norm_sq, (toDual ℝ Hilbert).symm.norm_map] at identity
  have coefficients : ∀ index, inner ℝ (basis index) ((toDual ℝ Hilbert).symm evaluation) =
      evaluation (basis index) := fun index => (real_inner_comm _ _).trans toDual_symm_apply
  simpa only [toDual_symm_apply, coefficients, ← sq] using identity

end
end IGSIII34.Spectral
