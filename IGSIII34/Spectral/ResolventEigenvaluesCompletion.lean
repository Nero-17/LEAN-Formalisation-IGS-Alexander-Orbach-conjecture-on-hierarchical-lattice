import IGSIII34.Spectral.CompactEigenvalueFinitenessCompletion
import IGSIII34.Spectral.AnchoredResolventCompletion
import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Set.Countable

/-! Positivity, the contraction bound and countability of the genuine compact
resolvent spectrum. The generator eigenvalues diverge outside finite sets. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open Filter InnerProductSpace
open scoped Topology

theorem anchoredL2Resolvent_norm_le_completion
    {Energy L2 : Type*}
    [NormedAddCommGroup Energy] [InnerProductSpace ℝ Energy] [CompleteSpace Energy]
    [NormedAddCommGroup L2] [InnerProductSpace ℝ L2] [CompleteSpace L2]
    (embedding : Energy →L[ℝ] L2) (anchorEvaluation : StrongDual ℝ Energy)
    (coercive : IsCoercive (anchoredResolventBilinearCompletion embedding anchorEvaluation))
    (energyNonnegative : ∀ function : Energy, 0 ≤ ‖function‖ ^ 2 - anchorEvaluation function ^ 2)
    (forcing : L2) :
    ‖anchoredL2ResolventCompletion embedding anchorEvaluation coercive forcing‖ ≤ ‖forcing‖ := by
  let solution := coercive.continuousLinearEquivOfBilin.symm (embedding.adjoint forcing)
  have identity := anchoredL2Resolvent_variational_completion embedding anchorEvaluation
    coercive forcing solution
  have squareBound : ‖embedding solution‖ ^ 2 ≤ inner ℝ forcing (embedding solution) := by
    rw [← identity, anchoredResolventBilinear_self_completion]
    linarith [energyNonnegative solution]
  have cauchy := real_inner_le_norm forcing (embedding solution)
  change ‖embedding solution‖ ≤ ‖forcing‖
  nlinarith [norm_nonneg (embedding solution), norm_nonneg forcing]

theorem compact_positive_injective_eigenvalues_completion
    {Hilbert Index : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    [CompleteSpace Hilbert] (operator : Hilbert →L[ℝ] Hilbert)
    (nonnegative : ∀ vector, 0 ≤ inner ℝ (operator vector) vector)
    (kernelZero : ∀ vector, operator vector = 0 → vector = 0)
    (contractive : ∀ vector, ‖operator vector‖ ≤ ‖vector‖)
    (vectors : Index → Hilbert) (orthonormal : Orthonormal ℝ vectors)
    (eigenvalues : Index → ℝ)
    (eigenvectors : ∀ index, operator (vectors index) = eigenvalues index • vectors index) :
    ∀ index, 0 < eigenvalues index ∧ eigenvalues index ≤ 1 := by
  intro index
  have innerValue : inner ℝ (operator (vectors index)) (vectors index) = eigenvalues index := by
    rw [eigenvectors index, inner_smul_left, real_inner_self_eq_norm_sq,
      orthonormal.norm_eq_one]
    simp
  have valueNonnegative : 0 ≤ eigenvalues index := innerValue ▸ nonnegative (vectors index)
  have valueNonzero : eigenvalues index ≠ 0 := by
    intro zero
    have vectorZero := kernelZero (vectors index) (by rw [eigenvectors index, zero, zero_smul])
    have normOne := orthonormal.norm_eq_one index
    rw [vectorZero, norm_zero] at normOne
    norm_num at normOne
  have upper := contractive (vectors index)
  rw [eigenvectors index, norm_smul, orthonormal.norm_eq_one, Real.norm_eq_abs, mul_one,
    abs_of_nonneg valueNonnegative] at upper
  exact ⟨lt_of_le_of_ne valueNonnegative (Ne.symm valueNonzero), upper⟩

theorem countable_compact_positive_eigenfamily_completion
    {Hilbert Index : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    [CompleteSpace Hilbert] (operator : Hilbert →L[ℝ] Hilbert)
    (compact : IsCompactOperator operator) (vectors : Index → Hilbert)
    (orthonormal : Orthonormal ℝ vectors) (eigenvalues : Index → ℝ)
    (positive : ∀ index, 0 < eigenvalues index)
    (eigenvectors : ∀ index, operator (vectors index) = eigenvalues index • vectors index) :
    Countable Index := by
  have finite (depth : ℕ) : {index | 1 / (depth + 1 : ℝ) ≤ |eigenvalues index|}.Finite :=
    compact_orthonormal_eigenvalues_finite_large_completion operator compact
      vectors orthonormal eigenvalues eigenvectors _ (by positivity)
  apply Set.countable_univ_iff.mp
  apply (Set.countable_iUnion (fun depth => (finite depth).countable)).mono
  intro index _
  obtain ⟨depth, below⟩ := exists_nat_one_div_lt (positive index)
  exact Set.mem_iUnion.mpr ⟨depth, below.le.trans (le_abs_self _)⟩

theorem compact_generator_eigenvalues_diverge_completion
    {Hilbert Index : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    [CompleteSpace Hilbert] (operator : Hilbert →L[ℝ] Hilbert)
    (compact : IsCompactOperator operator) (vectors : Index → Hilbert)
    (orthonormal : Orthonormal ℝ vectors) (eigenvalues : Index → ℝ)
    (positive : ∀ index, 0 < eigenvalues index)
    (upper : ∀ index, eigenvalues index ≤ 1)
    (eigenvectors : ∀ index, operator (vectors index) = eigenvalues index • vectors index) :
    (∀ index, 0 ≤ (eigenvalues index)⁻¹ - 1) ∧
      Tendsto (fun index => (eigenvalues index)⁻¹ - 1) cofinite atTop := by
  have inverseLower (index : Index) : 1 ≤ (eigenvalues index)⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ (positive index)).mpr
    simpa only [one_mul] using upper index
  refine ⟨fun index => by linarith [inverseLower index], tendsto_atTop.mpr ?_⟩
  intro bound
  by_cases boundNegative : bound < 0
  · exact Filter.Eventually.of_forall (fun index => by linarith [inverseLower index])
  have boundPositive : 0 < bound + 1 := by linarith
  have finite := compact_orthonormal_eigenvalues_finite_large_completion operator compact
    vectors orthonormal eigenvalues eigenvectors (1 / (bound + 1)) (by positivity)
  apply Filter.eventually_cofinite.mpr
  apply finite.subset
  intro index outside
  have generatorBelow : (eigenvalues index)⁻¹ - 1 < bound := lt_of_not_ge outside
  have multiplied := mul_le_mul_of_nonneg_left (show (eigenvalues index)⁻¹ ≤ bound + 1 by linarith)
    (positive index).le
  rw [mul_inv_cancel₀ (positive index).ne'] at multiplied
  have reciprocalBelow : 1 / (bound + 1) ≤ eigenvalues index :=
    (div_le_iff₀ boundPositive).mpr (by nlinarith)
  exact reciprocalBelow.trans (le_abs_self _)

end
end IGSIII34.Spectral
