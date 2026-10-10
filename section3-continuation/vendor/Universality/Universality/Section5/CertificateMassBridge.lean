import Universality.Section5.ActualAllocationMass
import Universality.Section5.CompositionFamily

set_option backward.isDefEq.respectTransparency false

namespace Universality.Section5
noncomputable section
open Matrix FiniteNetwork

theorem massPlaneLift_add (first second : Fin 2 → ℝ) :
    massPlaneLift (first + second) = massPlaneLift first + massPlaneLift second := by
  ext state
  cases state <;> simp [massPlaneLift, mul_add]

theorem massPlaneLift_sub (first second : Fin 2 → ℝ) :
    massPlaneLift (first - second) = massPlaneLift first - massPlaneLift second := by
  ext state
  cases state <;> simp [massPlaneLift, mul_sub]

theorem massPlaneLift_nsmul (coefficient : ℕ) (value : Fin 2 → ℝ) :
    massPlaneLift (coefficient • value) = coefficient • massPlaneLift value := by
  ext state
  cases state <;> simp [massPlaneLift, nsmul_eq_mul, mul_left_comm]

theorem baseKernel_massPlaneLift (value : Fin 2 → ℝ) :
    (2 * K3real + J3real) *ᵥ massPlaneLift value =
      (1 / 16 : ℝ) • massPlaneLift
        ((2 * outerKernelNumerator.map Int.cast + centralKernelNumerator.map Int.cast) *ᵥ value) := by
  rw [two_mul, Matrix.add_mulVec, Matrix.add_mulVec,
    K3real_massPlaneLift, J3real_massPlaneLift]
  simp only [two_mul, Matrix.add_mulVec, massPlaneLift_add, smul_add]

theorem baseKernel_pow_massPlaneLift (n : ℕ) (value : Fin 2 → ℝ) :
    (2 * K3real + J3real) ^ n *ᵥ massPlaneLift value =
      (1 / 16 : ℝ) ^ n • massPlaneLift
        ((2 * outerKernelNumerator.map Int.cast + centralKernelNumerator.map Int.cast) ^ n *ᵥ value) := by
  induction n generalizing value with
  | zero => simp
  | succ n induction_hypothesis =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, induction_hypothesis, Matrix.mulVec_smul,
        baseKernel_massPlaneLift, smul_smul, pow_succ',
        pow_succ' (2 * outerKernelNumerator.map Int.cast + centralKernelNumerator.map Int.cast),
        ← Matrix.mulVec_mulVec]
      rw [mul_comm ((1 / 16 : ℝ) ^ n) (1 / 16)]

theorem incrementKernel_massPlaneLift (value : Fin 2 → ℝ) :
    (2 * K3real + J3real - 1) *ᵥ massPlaneLift value =
      (1 / 16 : ℝ) • massPlaneLift
        ((2 * outerKernelNumerator.map Int.cast + centralKernelNumerator.map Int.cast - 16) *ᵥ value) := by
  rw [Matrix.sub_mulVec, baseKernel_massPlaneLift, Matrix.one_mulVec,
    Matrix.sub_mulVec, Matrix.ofNat_mulVec, massPlaneLift_sub, massPlaneLift_smul, smul_sub,
    smul_smul]
  norm_num

theorem weightedWords_massPlaneLift (n : ℕ) (words : List (List Bool))
    (allocation : List Bool → ℕ) (lengths : ∀ word ∈ words, word.length = n)
    (value : Fin 2 → ℝ) :
    (words.map (fun word => allocation word • wordProduct K3real J3real word)).sum *ᵥ
        massPlaneLift value =
      (1 / 16 : ℝ) ^ n • massPlaneLift
        ((words.map (fun word => allocation word •
          wordProduct (outerKernelNumerator.map Int.cast)
            (centralKernelNumerator.map Int.cast) word)).sum *ᵥ value) := by
  induction words with
  | nil => ext state; cases state <;> simp [massPlaneLift]
  | cons word words induction_hypothesis =>
      rw [List.map_cons, List.sum_cons, Matrix.add_mulVec, Matrix.smul_mulVec,
        wordProduct_massPlaneLift, lengths word (by simp),
        induction_hypothesis (by intro other member; exact lengths other (by simp [member]))]
      simp only [List.map_cons, List.sum_cons, Matrix.add_mulVec, Matrix.smul_mulVec,
        massPlaneLift_add, massPlaneLift_nsmul, smul_add]
      rw [smul_comm]

/-- The exact integer numerator, including the final factor of 16. -/
def allocationMassNumerator (n : ℕ) (allocation : List Bool → ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  16 • (2 * outerKernelNumerator + centralKernelNumerator) ^ n +
    ((binaryWords n).map (fun word => allocation word •
      (wordProduct outerKernelNumerator centralKernelNumerator word *
        (2 * outerKernelNumerator + centralKernelNumerator - 16)))).sum

theorem allocation_massMatrix_normalized_action (n : ℕ) (allocation : List Bool → ℕ)
    (capacity : ∀ word ∈ binaryWords n, allocation word ≤ 2 ^ zeroCount word)
    (value : Fin 2 → ℝ) :
    (allocatedExpression n (allocationDecoration allocation)).rule.network.massMatrix (1 / 2) *ᵥ
        massPlaneLift value =
      (1 / 16 : ℝ) ^ (n + 1) • massPlaneLift
        ((16 • (2 * outerKernelNumerator.map Int.cast + centralKernelNumerator.map Int.cast) ^ n +
          ((binaryWords n).map (fun word => allocation word •
            wordProduct (outerKernelNumerator.map Int.cast) (centralKernelNumerator.map Int.cast) word)).sum *
              (2 * outerKernelNumerator.map Int.cast + centralKernelNumerator.map Int.cast - 16)) *ᵥ value) := by
  rw [allocation_massMatrix n allocation capacity, Matrix.add_mulVec,
    baseKernel_pow_massPlaneLift, ← Matrix.mulVec_mulVec,
    incrementKernel_massPlaneLift, Matrix.mulVec_smul,
    weightedWords_massPlaneLift n (binaryWords n) allocation
      (by intro word member; exact word_length_of_mem_binaryWords member)]
  simp only [smul_smul, Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
    massPlaneLift_add, massPlaneLift_nsmul, smul_add, pow_succ]
  ext state
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul,
    Pi.mul_apply, Pi.natCast_apply]
  ring

theorem integerWordProduct_cast (word : List Bool) :
    (wordProduct outerKernelNumerator centralKernelNumerator word).map (Int.cast : ℤ → ℝ) =
      wordProduct (outerKernelNumerator.map Int.cast) (centralKernelNumerator.map Int.cast) word := by
  change (Int.castRingHom ℝ).mapMatrix
      (wordProduct outerKernelNumerator centralKernelNumerator word) = _
  induction word with
  | nil => exact map_one _
  | cons letter word induction_hypothesis =>
      cases letter <;> simp only [wordProduct, map_mul, induction_hypothesis]
      <;> rfl

theorem allocationMassNumerator_cast (n : ℕ) (allocation : List Bool → ℕ) :
    (allocationMassNumerator n allocation).map (Int.cast : ℤ → ℝ) =
      16 • (2 * outerKernelNumerator.map Int.cast + centralKernelNumerator.map Int.cast) ^ n +
        ((binaryWords n).map (fun word => allocation word •
          wordProduct (outerKernelNumerator.map Int.cast) (centralKernelNumerator.map Int.cast) word)).sum *
            (2 * outerKernelNumerator.map Int.cast + centralKernelNumerator.map Int.cast - 16) := by
  change (Int.castRingHom ℝ).mapMatrix (allocationMassNumerator n allocation) = _
  simp only [allocationMassNumerator, map_add, map_nsmul, map_pow, map_mul, map_ofNat,
    map_list_sum, List.map_map, Function.comp_def, map_sub]
  change 16 • (2 * outerKernelNumerator.map Int.cast + centralKernelNumerator.map Int.cast) ^ n +
      ((binaryWords n).map (fun word => allocation word •
        ((wordProduct outerKernelNumerator centralKernelNumerator word).map (Int.cast : ℤ → ℝ) *
          (2 * outerKernelNumerator.map Int.cast + centralKernelNumerator.map Int.cast - 16)))).sum = _
  simp only [integerWordProduct_cast, ← smul_mul_assoc]
  rw [List.sum_map_mul_right]

theorem allocation_massMatrix_integer_action (n : ℕ) (allocation : List Bool → ℕ)
    (capacity : ∀ word ∈ binaryWords n, allocation word ≤ 2 ^ zeroCount word)
    (value : Fin 2 → ℝ) :
    (allocatedExpression n (allocationDecoration allocation)).rule.network.massMatrix (1 / 2) *ᵥ
        massPlaneLift value =
      (1 / 16 : ℝ) ^ (n + 1) •
        massPlaneLift ((allocationMassNumerator n allocation).map Int.cast *ᵥ value) := by
  rw [allocationMassNumerator_cast]
  exact allocation_massMatrix_normalized_action n allocation capacity value

theorem integer_eigenvector_cast (matrix : Matrix (Fin 2) (Fin 2) ℤ)
    (value : Fin 2 → ℤ) (eigenvalue : ℤ) (eigenvector : matrix *ᵥ value = eigenvalue • value) :
    matrix.map (Int.cast : ℤ → ℝ) *ᵥ (fun index => (value index : ℝ)) =
      (eigenvalue : ℝ) • (fun index => (value index : ℝ)) := by
  ext index
  have equality := congrArg (fun vector : Fin 2 → ℤ => (vector index : ℝ)) eigenvector
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] using equality

/-- A finite integer certificate gives the mass response of the actual allocated graph. -/
theorem allocation_massMatrix_eigenvector (n base : ℕ) (allocation : List Bool → ℕ)
    (capacity : ∀ word ∈ binaryWords n, allocation word ≤ 2 ^ zeroCount word)
    (certificate : allocationMassNumerator n allocation *ᵥ (![55, 23] : Fin 2 → ℤ) =
      (16 ^ (n + 1) * (base : ℤ) ^ 219) • (![55, 23] : Fin 2 → ℤ)) :
    (allocatedExpression n (allocationDecoration allocation)).rule.network.massMatrix (1 / 2) *ᵥ
        certificateWeight = (base : ℝ) ^ 219 • certificateWeight := by
  have vector_cast : (fun index => ((![55, 23] : Fin 2 → ℤ) index : ℝ)) =
      (![55, 23] : Fin 2 → ℝ) := by
    ext index
    fin_cases index <;> norm_num
  have lifted_vector : massPlaneLift (![55, 23] : Fin 2 → ℝ) = certificateWeight := by
    ext state
    cases state <;> norm_num [massPlaneLift, certificateWeight]
  have real_eigenvector := integer_eigenvector_cast (allocationMassNumerator n allocation)
    (![55, 23] : Fin 2 → ℤ) (16 ^ (n + 1) * (base : ℤ) ^ 219) certificate
  rw [vector_cast] at real_eigenvector
  simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast] at real_eigenvector
  rw [← lifted_vector, allocation_massMatrix_integer_action n allocation capacity,
    real_eigenvector, massPlaneLift_smul, smul_smul]
  have normalization : (1 / 16 : ℝ) ^ (n + 1) *
      ((16 : ℝ) ^ (n + 1) * (base : ℝ) ^ 219) = (base : ℝ) ^ 219 := by
    rw [← mul_assoc, ← mul_pow]
    norm_num
  rw [normalization]

end
end Universality.Section5
