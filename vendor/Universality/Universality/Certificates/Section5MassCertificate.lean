import Universality.Certificates.Section5MatrixEvaluationCast
import Universality.Certificates.Section5Sums
import Universality.Section5.CertificateMassBridge
import Universality.Certificates.Section5MatrixRepairEvaluation
import Universality.Certificates.Section5MatrixStreamCorrect

/-! Assembly of the finite integer mass identity. Numerical evaluator equalities
remain explicit until their generated kernel proofs are imported. -/

namespace Universality.Certificates
open Matrix

def initialOrderedMass (depth : ℕ) (rows : List InitialAllocationRow) : Fin 2 → ℤ :=
  ((binaryWords depth).map (fun word => (initialAllocation rows word : ℤ) •
    wordProduct outerKernelNumerator centralKernelNumerator word)).sum *ᵥ ![3139, 1313]

def packetOrderedMass (packets : List CorrectionPacket) : Fin 2 → ℤ :=
  (packets.map (fun packet => (packet.coefficient * 18 ^ packet.layer) •
    ((!![-6, -6; 3, 6] * wordProduct outerKernelNumerator centralKernelNumerator
      (correctionTail packet.first packet.repeated packet.remaining)) *ᵥ ![3139, 1313]))).sum

theorem list_matrix_sum_mulVec {α R : Type*} [Semiring R]
    (items : List α) (matrix : α → Matrix (Fin 2) (Fin 2) R) (vector : Fin 2 → R) :
    (items.map matrix).sum *ᵥ vector =
      (items.map (fun item => matrix item *ᵥ vector)).sum := by
  induction items with
  | nil => simp
  | cons item items ih => simp [Matrix.add_mulVec, ih]

theorem integerIncrement_vector :
    (2 * outerKernelNumerator + centralKernelNumerator - 16) *ᵥ
      (![55, 23] : Fin 2 → ℤ) = ![3139, 1313] := by
  ext index
  fin_cases index <;>
    norm_num [outerKernelNumerator, centralKernelNumerator, Matrix.mulVec,
      dotProduct, Fin.sum_univ_two, Matrix.mul_apply, Matrix.ofNat_apply]

theorem CompressedAllocation.mass_numerator_decomposition (certificate : CompressedAllocation)
    (checked : certificate.capacityValid) :
    Section5.allocationMassNumerator certificate.depth certificate.allocation *ᵥ
        (![55, 23] : Fin 2 → ℤ) =
      16 • ((2 * outerKernelNumerator + centralKernelNumerator) ^ certificate.depth *ᵥ
        (![55, 23] : Fin 2 → ℤ)) +
      initialOrderedMass certificate.depth certificate.rows + packetOrderedMass certificate.packets := by
  have corrected := certificate.corrected_matrix_sum checked
    (2 * outerKernelNumerator + centralKernelNumerator - 16)
  simp only [natCast_zsmul] at corrected
  unfold Section5.allocationMassNumerator
  rw [corrected, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec]
  simp only [initialOrderedMass, packetOrderedMass, list_matrix_sum_mulVec,
    Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, integerIncrement_vector]
  exact (add_assoc _ _ _).symm

theorem initialOrderedMass_natCast (depth : ℕ) (rows : List InitialAllocationRow) :
    (fun index => ((((binaryWords depth).map (fun word => initialAllocation rows word •
      wordProduct naturalOuterKernel naturalCentralKernel word)).sum *ᵥ initialMassVector) index : ℤ)) =
      initialOrderedMass depth rows := by
  have matrix_cast :
      (((binaryWords depth).map (fun word => initialAllocation rows word •
        wordProduct naturalOuterKernel naturalCentralKernel word)).sum).map (Nat.castRingHom ℤ) =
      ((binaryWords depth).map (fun word => initialAllocation rows word •
        wordProduct outerKernelNumerator centralKernelNumerator word)).sum := by
    change (Nat.castRingHom ℤ).mapMatrix _ = _
    simp only [map_list_sum, List.map_map, Function.comp_def, map_nsmul, ringHom_wordProduct,
      RingHom.mapMatrix_apply, naturalOuterKernel_cast, naturalCentralKernel_cast]
  ext index
  change (Nat.castRingHom ℤ) ((_ *ᵥ initialMassVector) index) = _
  rw [RingHom.map_mulVec, matrix_cast, initialMassVector_cast]
  simp only [initialOrderedMass, natCast_zsmul]

def massEvaluationWithInitial (depth : ℕ) (packets : List CorrectionPacket)
    (initialValue : ℕ × ℕ) : ℤ × ℤ :=
  addIntegerMassPairs
    (addIntegerMassPairs (baselineMassEvaluation depth)
      ((initialValue.1 : ℤ), (initialValue.2 : ℤ)))
    (correctionsMassEvaluation packets)

def massCertificateValue (depth base : ℕ) : ℤ × ℤ :=
  (16 ^ (depth + 1) * (base : ℤ) ^ 219 * 55,
    16 ^ (depth + 1) * (base : ℤ) ^ 219 * 23)

theorem integerPairVector_massCertificateValue (depth base : ℕ) :
    integerPairVector (massCertificateValue depth base) =
      (16 ^ (depth + 1) * (base : ℤ) ^ 219) • (![55, 23] : Fin 2 → ℤ) := by
  ext index
  fin_cases index <;> rfl

theorem CompressedAllocation.mass_certificate_from_initial (certificate : CompressedAllocation)
    (checked : certificate.capacityValid) (base : ℕ) (initialValue : ℕ × ℕ)
    (initial_checked : integerPairVector ((initialValue.1 : ℤ), (initialValue.2 : ℤ)) =
      initialOrderedMass certificate.depth certificate.rows)
    (numerical_checked : massEvaluationWithInitial certificate.depth certificate.packets initialValue =
      massCertificateValue certificate.depth base) :
    Section5.allocationMassNumerator certificate.depth certificate.allocation *ᵥ
      (![55, 23] : Fin 2 → ℤ) =
      (16 ^ (certificate.depth + 1) * (base : ℤ) ^ 219) • (![55, 23] : Fin 2 → ℤ) := by
  have equality := congrArg integerPairVector numerical_checked
  rw [massEvaluationWithInitial, integerPairVector_add, integerPairVector_add,
    baselineMassEvaluation_correct, correctionsMassEvaluation_correct,
    initial_checked, integerPairVector_massCertificateValue] at equality
  rw [certificate.mass_numerator_decomposition checked]
  simpa only [packetOrderedMass, two_smul, two_mul] using equality

theorem initialMassEvaluation_integer_correct (depth : ℕ) (rows : List InitialAllocationRow) :
    integerPairVector (((initialMassEvaluation depth rows).1 : ℤ),
      ((initialMassEvaluation depth rows).2 : ℤ)) = initialOrderedMass depth rows := by
  have equality := congrArg (fun vector : Fin 2 → ℕ => fun index => (vector index : ℤ))
    (initialMassEvaluation_correct depth rows)
  rw [initialOrderedMass_natCast] at equality
  convert equality using 1
  ext index
  fin_cases index <;> rfl

theorem CompressedAllocation.mass_certificate (certificate : CompressedAllocation)
    (checked : certificate.capacityValid) (base : ℕ) (initialValue : ℕ × ℕ)
    (initial_checked : initialMassEvaluation certificate.depth certificate.rows = initialValue)
    (numerical_checked : massEvaluationWithInitial certificate.depth certificate.packets initialValue =
      massCertificateValue certificate.depth base) :
    Section5.allocationMassNumerator certificate.depth certificate.allocation *ᵥ
      (![55, 23] : Fin 2 → ℤ) =
      (16 ^ (certificate.depth + 1) * (base : ℤ) ^ 219) • (![55, 23] : Fin 2 → ℤ) := by
  apply certificate.mass_certificate_from_initial checked base initialValue _ numerical_checked
  rw [← initial_checked]
  exact initialMassEvaluation_integer_correct certificate.depth certificate.rows

#print axioms CompressedAllocation.mass_certificate

end Universality.Certificates

