import Universality.Certificates.Section5MatrixStream
import Init.Data.Nat.Bitwise.Lemmas

namespace Universality.Certificates

def packedBitDigit (bits zeros packed : ℕ) : ℕ :=
  (packed >>> (bits * zeros)) &&& (2 ^ bits - 1)

theorem packedBitDigit_eq (bits zeros packed : ℕ) :
    packedBitDigit bits zeros packed = packed / (2 ^ bits) ^ zeros % 2 ^ bits := by
  rw [packedBitDigit, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]

def packedGroupedBits (bits depth zeros : ℕ) (packed : ℕ × ℕ) : ℕ × ℕ :=
  if zeros ≤ depth then
    (packedBitDigit bits zeros packed.1, packedBitDigit bits zeros packed.2)
  else (0, 0)

theorem packedGroupedBits_eq (bits depth zeros : ℕ) (packed : ℕ × ℕ) :
    packedGroupedBits bits depth zeros packed = packedGroupedFromRow (2 ^ bits) depth zeros packed := by
  simp only [packedGroupedBits, packedGroupedFromRow, packedBitDigit_eq]

def packedBinomialBits (bits depth zeros packed : ℕ) : ℕ :=
  if zeros ≤ depth then packedBitDigit bits zeros packed else 0

theorem packedBinomialBits_eq (bits depth zeros packed : ℕ) :
    packedBinomialBits bits depth zeros packed = packedBinomialFromRow (2 ^ bits) depth zeros packed := by
  simp only [packedBinomialBits, packedBinomialFromRow, packedBitDigit_eq]

def runLexMassBitStream (bits : ℕ) : ℕ → (ℕ × ℕ) → ℕ → List LexMassState → ℕ × ℕ
  | 0, _, _, states => sumMassPairs (states.map terminalLexMass)
  | childDepth + 1, packed, packedCounts, states =>
      let childPacked := packedPreviousVector (2 ^ bits) packed
      let childCounts := packedCounts / (2 ^ bits + 1)
      let next := advanceLexStates
        (fun zeros => packedGroupedBits bits childDepth zeros childPacked)
        (fun zeros => packedBinomialBits bits childDepth zeros childCounts) states
      addMassPairs next.1 (runLexMassBitStream bits childDepth childPacked childCounts next.2)

theorem runLexMassBitStream_eq (bits depth : ℕ) (packed : ℕ × ℕ)
    (packedCounts : ℕ) (states : List LexMassState) :
    runLexMassBitStream bits depth packed packedCounts states =
      runLexMassStream (2 ^ bits) depth packed packedCounts states := by
  induction depth generalizing packed packedCounts states with
  | zero => rfl
  | succ depth ih =>
      simp only [runLexMassBitStream, runLexMassStream, packedGroupedBits_eq,
        packedBinomialBits_eq, ih]

def initialFloorMassBits (bits childDepth : ℕ) (packed : ℕ × ℕ)
    (rows : List InitialAllocationRow) : ℕ × ℕ :=
  sumMassPairs ((List.range (childDepth + 2)).map fun zeros =>
    addMassPairs
      (if zeros = 0 then (0, 0) else
        scaleMassPair (rows[zeros]!).firstFalse
          (KernelPrefix.identity.rightOuter.action
            (packedGroupedBits bits childDepth (zeros - 1) packed)))
      (scaleMassPair (rows[zeros]!).firstTrue
        (KernelPrefix.identity.rightCentral.action
          (packedGroupedBits bits childDepth zeros packed))))

theorem initialFloorMassBits_eq (bits childDepth : ℕ) (packed : ℕ × ℕ)
    (rows : List InitialAllocationRow) :
    initialFloorMassBits bits childDepth packed rows = initialFloorMass (2 ^ bits) childDepth packed rows := by
  simp only [initialFloorMassBits, initialFloorMass, packedGroupedBits_eq]

def initialMassEvaluationBits (depth : ℕ) (rows : List InitialAllocationRow) : ℕ × ℕ :=
  let bits := 6 * (depth + 1) + 12
  let base := 2 ^ bits
  let packed := packedInitialVector base depth
  let lexMass := runLexMassBitStream bits depth packed ((base + 1) ^ depth)
    (initialLexStates depth rows)
  let floorMass := match depth with
    | 0 => scaleMassPair (rows[0]!).firstFalse (3139, 1313)
    | childDepth + 1 => initialFloorMassBits bits childDepth (packedPreviousVector base packed) rows
  addMassPairs floorMass lexMass

theorem initialMassEvaluationBits_eq (depth : ℕ) (rows : List InitialAllocationRow) :
    initialMassEvaluationBits depth rows = initialMassEvaluation depth rows := by
  simp only [initialMassEvaluationBits, initialMassEvaluation, matrixPackingBase,
    runLexMassBitStream_eq]
  cases depth <;> simp only [initialFloorMassBits_eq]

#print axioms initialMassEvaluationBits_eq

end Universality.Certificates

