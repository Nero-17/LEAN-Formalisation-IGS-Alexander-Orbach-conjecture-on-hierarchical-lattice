import Universality.Certificates.Section5MatrixEvaluation
import Mathlib.Data.Matrix.Basic

namespace Universality.Certificates
open Matrix

theorem ringHom_wordProduct {R S : Type*} [Semiring R] [Semiring S]
    (hom : R →+* S) (outer central : R) (word : List Bool) :
    hom (wordProduct outer central word) = wordProduct (hom outer) (hom central) word := by
  induction word with
  | nil => simp [wordProduct]
  | cons bit word ih => cases bit <;> simp [wordProduct, ih]

theorem ringHom_groupedWordSum {R S : Type*} [Semiring R] [Semiring S]
    (hom : R →+* S) (outer central : R) (depth zeros : ℕ) :
    hom (groupedWordSum outer central depth zeros) =
      groupedWordSum (hom outer) (hom central) depth zeros := by
  simp [groupedWordSum, map_list_sum, List.map_map, Function.comp_def, ringHom_wordProduct, apply_ite]

theorem ringHom_lexPrefixWordSum {R S : Type*} [Semiring R] [Semiring S]
    (hom : R →+* S) (outer central : R) (depth zeros cutoff : ℕ) :
    hom (lexPrefixWordSum outer central depth zeros cutoff) =
      lexPrefixWordSum (hom outer) (hom central) depth zeros cutoff := by
  simp [lexPrefixWordSum, map_list_sum, List.map_map, Function.comp_def, ringHom_wordProduct, apply_ite]

@[simp] theorem naturalOuterKernel_cast :
    naturalOuterKernel.map (Nat.castRingHom ℤ) = outerKernelNumerator := by
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

@[simp] theorem naturalCentralKernel_cast :
    naturalCentralKernel.map (Nat.castRingHom ℤ) = centralKernelNumerator := by
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

@[simp] theorem initialMassVector_cast :
    (Nat.castRingHom ℤ) ∘ initialMassVector = (![3139, 1313] : Fin 2 → ℤ) := by
  ext index
  fin_cases index <;> rfl

theorem groupedWordSum_natural_cast (depth zeros : ℕ) :
    (groupedWordSum naturalOuterKernel naturalCentralKernel depth zeros).map (Nat.castRingHom ℤ) =
      groupedWordSum outerKernelNumerator centralKernelNumerator depth zeros := by
  simpa only [RingHom.mapMatrix_apply, naturalOuterKernel_cast, naturalCentralKernel_cast] using
    ringHom_groupedWordSum (Nat.castRingHom ℤ).mapMatrix
      naturalOuterKernel naturalCentralKernel depth zeros

theorem lexPrefixWordSum_natural_cast (depth zeros cutoff : ℕ) :
    (lexPrefixWordSum naturalOuterKernel naturalCentralKernel depth zeros cutoff).map
      (Nat.castRingHom ℤ) =
      lexPrefixWordSum outerKernelNumerator centralKernelNumerator depth zeros cutoff := by
  simpa only [RingHom.mapMatrix_apply, naturalOuterKernel_cast, naturalCentralKernel_cast] using
    ringHom_lexPrefixWordSum (Nat.castRingHom ℤ).mapMatrix
      naturalOuterKernel naturalCentralKernel depth zeros cutoff

theorem groupedMassVector_cast (depth zeros : ℕ) :
    (fun index => (groupedMassVector depth zeros index : ℤ)) =
      groupedWordSum outerKernelNumerator centralKernelNumerator depth zeros *ᵥ
        (![3139, 1313] : Fin 2 → ℤ) := by
  ext index
  change (Nat.castRingHom ℤ) ((groupedWordSum naturalOuterKernel naturalCentralKernel
    depth zeros *ᵥ initialMassVector) index) = _
  rw [RingHom.map_mulVec, groupedWordSum_natural_cast, initialMassVector_cast]

theorem lexPrefixMassVector_cast (depth zeros cutoff : ℕ) :
    (fun index => ((lexPrefixWordSum naturalOuterKernel naturalCentralKernel depth zeros cutoff *ᵥ
      initialMassVector) index : ℤ)) =
      lexPrefixWordSum outerKernelNumerator centralKernelNumerator depth zeros cutoff *ᵥ
        (![3139, 1313] : Fin 2 → ℤ) := by
  ext index
  change (Nat.castRingHom ℤ) ((lexPrefixWordSum naturalOuterKernel naturalCentralKernel
    depth zeros cutoff *ᵥ initialMassVector) index) = _
  rw [RingHom.map_mulVec, lexPrefixWordSum_natural_cast, initialMassVector_cast]

end Universality.Certificates
