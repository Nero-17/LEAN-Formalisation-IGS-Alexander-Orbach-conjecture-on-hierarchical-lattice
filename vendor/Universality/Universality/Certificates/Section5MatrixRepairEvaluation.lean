import Universality.Certificates.Section5MatrixEvaluationCast
import Universality.Certificates.Section5Sums

namespace Universality.Certificates
open Matrix

def integerPairVector (value : ℤ × ℤ) : Fin 2 → ℤ := ![value.1, value.2]

def integerKernelStep (bit : Bool) (value : ℤ × ℤ) : ℤ × ℤ :=
  if bit then (9 * value.1 + 12 * value.2, 3 * value.1 + 6 * value.2)
  else (22 * value.1 + 18 * value.2, 5 * value.1 + 18 * value.2)

def integerKernelPower (bit : Bool) : ℕ → (ℤ × ℤ) → ℤ × ℤ
  | 0, value => value
  | power + 1, value => integerKernelStep bit (integerKernelPower bit power value)

theorem integerKernelStep_correct (bit : Bool) (value : ℤ × ℤ) :
    integerPairVector (integerKernelStep bit value) =
      (if bit then centralKernelNumerator else outerKernelNumerator) *ᵥ integerPairVector value := by
  ext index
  cases bit <;> fin_cases index <;>
    simp [integerKernelStep, integerPairVector, centralKernelNumerator, outerKernelNumerator,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem integerKernelPower_correct (bit : Bool) (power : ℕ) (value : ℤ × ℤ) :
    integerPairVector (integerKernelPower bit power value) =
      wordProduct outerKernelNumerator centralKernelNumerator (List.replicate power bit) *ᵥ
        integerPairVector value := by
  induction power with
  | zero => simp [integerKernelPower, wordProduct]
  | succ power ih =>
      rw [integerKernelPower, integerKernelStep_correct, ih, List.replicate_succ]
      cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte, wordProduct, Matrix.mulVec_mulVec]

def correctionTailVector (packet : CorrectionPacket) : ℤ × ℤ :=
  integerKernelStep packet.first
    (integerKernelPower packet.repeated (packet.remaining + 1) (3139, 1313))

theorem correctionTailVector_correct (packet : CorrectionPacket) :
    integerPairVector (correctionTailVector packet) =
      wordProduct outerKernelNumerator centralKernelNumerator
        (correctionTail packet.first packet.repeated packet.remaining) *ᵥ
          (![3139, 1313] : Fin 2 → ℤ) := by
  rw [correctionTailVector, integerKernelStep_correct, integerKernelPower_correct]
  unfold correctionTail
  cases packet.first <;> simp only [Bool.false_eq_true, ↓reduceIte, wordProduct,
    Matrix.mulVec_mulVec, integerPairVector]

def correctionMassEvaluation (packet : CorrectionPacket) : ℤ × ℤ :=
  let value := correctionTailVector packet
  let coefficient := packet.coefficient * 18 ^ packet.layer
  (coefficient * (-6 * value.1 - 6 * value.2),
    coefficient * (3 * value.1 + 6 * value.2))

theorem correctionMassEvaluation_correct (packet : CorrectionPacket) :
    integerPairVector (correctionMassEvaluation packet) =
      (packet.coefficient * 18 ^ packet.layer) •
        ((!![-6, -6; 3, 6] * wordProduct outerKernelNumerator centralKernelNumerator
          (correctionTail packet.first packet.repeated packet.remaining)) *ᵥ
            (![3139, 1313] : Fin 2 → ℤ)) := by
  rw [← Matrix.mulVec_mulVec, ← correctionTailVector_correct]
  ext index
  fin_cases index <;>
    simp [correctionMassEvaluation, integerPairVector, sub_eq_add_neg, mul_comm]

def addIntegerMassPairs (first second : ℤ × ℤ) : ℤ × ℤ :=
  (first.1 + second.1, first.2 + second.2)

def correctionsMassEvaluation : List CorrectionPacket → ℤ × ℤ
  | [] => (0, 0)
  | packet :: packets => addIntegerMassPairs (correctionMassEvaluation packet)
      (correctionsMassEvaluation packets)

theorem integerPairVector_add (first second : ℤ × ℤ) :
    integerPairVector (addIntegerMassPairs first second) =
      integerPairVector first + integerPairVector second := by
  ext index
  fin_cases index <;> rfl

theorem correctionsMassEvaluation_correct (packets : List CorrectionPacket) :
    integerPairVector (correctionsMassEvaluation packets) =
      (packets.map fun packet => (packet.coefficient * 18 ^ packet.layer) •
        ((!![-6, -6; 3, 6] * wordProduct outerKernelNumerator centralKernelNumerator
          (correctionTail packet.first packet.repeated packet.remaining)) *ᵥ
            (![3139, 1313] : Fin 2 → ℤ))).sum := by
  induction packets with
  | nil => ext index; fin_cases index <;> rfl
  | cons packet packets ih =>
      simp only [correctionsMassEvaluation, integerPairVector_add,
        correctionMassEvaluation_correct, ih, List.map_cons, List.sum_cons]

def baselineMassVector : ℕ → ℤ × ℤ
  | 0 => (55, 23)
  | depth + 1 =>
      let value := baselineMassVector depth
      (53 * value.1 + 48 * value.2, 13 * value.1 + 42 * value.2)

theorem baselineMassVector_correct (depth : ℕ) :
    integerPairVector (baselineMassVector depth) =
      (2 • outerKernelNumerator + centralKernelNumerator) ^ depth *ᵥ
        (![55, 23] : Fin 2 → ℤ) := by
  induction depth with
  | zero => simp [baselineMassVector, integerPairVector]
  | succ depth ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih]
      ext index
      fin_cases index <;>
        simp [baselineMassVector, integerPairVector, outerKernelNumerator, centralKernelNumerator,
          Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def baselineMassEvaluation (depth : ℕ) : ℤ × ℤ :=
  let value := baselineMassVector depth
  (16 * value.1, 16 * value.2)

theorem baselineMassEvaluation_correct (depth : ℕ) :
    integerPairVector (baselineMassEvaluation depth) =
      (16 : ℕ) • ((2 • outerKernelNumerator + centralKernelNumerator) ^ depth *ᵥ
        (![55, 23] : Fin 2 → ℤ)) := by
  rw [← baselineMassVector_correct]
  ext index
  fin_cases index <;> simp [baselineMassEvaluation, integerPairVector]

end Universality.Certificates
