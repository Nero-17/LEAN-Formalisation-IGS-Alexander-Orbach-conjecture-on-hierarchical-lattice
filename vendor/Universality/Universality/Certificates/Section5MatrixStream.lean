import Universality.Certificates.Section5MatrixEvaluation

/-!
# A descending stream for the initial mass sum

Only the current packed grouped row, the current packed binomial row, and one
accumulated matrix per remainder are retained.  In particular, the computation
does not store a quadratic table of large integer vectors.
-/

namespace Universality.Certificates

structure KernelPrefix where
  upperLeft : ℕ
  upperRight : ℕ
  lowerLeft : ℕ
  lowerRight : ℕ
  deriving Inhabited, DecidableEq

def KernelPrefix.identity : KernelPrefix := ⟨1, 0, 0, 1⟩

def KernelPrefix.toMatrix (accumulated : KernelPrefix) : Matrix (Fin 2) (Fin 2) ℕ :=
  !![accumulated.upperLeft, accumulated.upperRight; accumulated.lowerLeft, accumulated.lowerRight]

def KernelPrefix.rightOuter (accumulated : KernelPrefix) : KernelPrefix :=
  ⟨22 * accumulated.upperLeft + 5 * accumulated.upperRight,
    18 * accumulated.upperLeft + 18 * accumulated.upperRight,
    22 * accumulated.lowerLeft + 5 * accumulated.lowerRight,
    18 * accumulated.lowerLeft + 18 * accumulated.lowerRight⟩

def KernelPrefix.rightCentral (accumulated : KernelPrefix) : KernelPrefix :=
  ⟨9 * accumulated.upperLeft + 3 * accumulated.upperRight,
    12 * accumulated.upperLeft + 6 * accumulated.upperRight,
    9 * accumulated.lowerLeft + 3 * accumulated.lowerRight,
    12 * accumulated.lowerLeft + 6 * accumulated.lowerRight⟩

def KernelPrefix.action (accumulated : KernelPrefix) (vector : ℕ × ℕ) : ℕ × ℕ :=
  (accumulated.upperLeft * vector.1 + accumulated.upperRight * vector.2,
    accumulated.lowerLeft * vector.1 + accumulated.lowerRight * vector.2)

def addMassPairs (left right : ℕ × ℕ) : ℕ × ℕ :=
  (left.1 + right.1, left.2 + right.2)

def scaleMassPair (coefficient : ℕ) (vector : ℕ × ℕ) : ℕ × ℕ :=
  (coefficient * vector.1, coefficient * vector.2)

def sumMassPairs : List (ℕ × ℕ) → ℕ × ℕ
  | [] => (0, 0)
  | value :: rest => addMassPairs value (sumMassPairs rest)

structure LexMassState where
  remainingZeros : ℕ
  remainder : ℕ
  accumulated : KernelPrefix
  deriving Inhabited, DecidableEq

def advanceLexState (grouped : ℕ → ℕ × ℕ) (counts : ℕ → ℕ)
    (state : LexMassState) : (ℕ × ℕ) × LexMassState :=
  if state.remainder = 0 then ((0, 0), state) else
    let firstCount := if state.remainingZeros = 0 then 0 else counts (state.remainingZeros - 1)
    if state.remainder ≤ firstCount then
      ((0, 0), ⟨state.remainingZeros - 1, state.remainder, state.accumulated.rightOuter⟩)
    else
      (if state.remainingZeros = 0 then (0, 0) else
          state.accumulated.rightOuter.action (grouped (state.remainingZeros - 1)),
        ⟨state.remainingZeros, state.remainder - firstCount, state.accumulated.rightCentral⟩)

def advanceLexStates (grouped : ℕ → ℕ × ℕ) (counts : ℕ → ℕ) :
    List LexMassState → (ℕ × ℕ) × List LexMassState
  | [] => ((0, 0), [])
  | state :: rest =>
      let current := advanceLexState grouped counts state
      let remaining := advanceLexStates grouped counts rest
      (addMassPairs current.1 remaining.1, current.2 :: remaining.2)

def terminalLexMass (state : LexMassState) : ℕ × ℕ :=
  if state.remainingZeros = 0 ∧ 0 < state.remainder then state.accumulated.action (3139, 1313)
  else (0, 0)

def runLexMassStream (base : ℕ) : ℕ → (ℕ × ℕ) → ℕ → List LexMassState → ℕ × ℕ
  | 0, _, _, states => sumMassPairs (states.map terminalLexMass)
  | childDepth + 1, packed, packedCounts, states =>
      let childPacked := packedPreviousVector base packed
      let childCounts := packedCounts / (base + 1)
      let next := advanceLexStates
        (fun zeros => packedGroupedFromRow base childDepth zeros childPacked)
        (fun zeros => packedBinomialFromRow base childDepth zeros childCounts) states
      addMassPairs next.1 (runLexMassStream base childDepth childPacked childCounts next.2)

def initialLexStates (depth : ℕ) (rows : List InitialAllocationRow) : List LexMassState :=
  (List.range (depth + 1)).map fun zeros =>
    ⟨zeros, (rows[zeros]!).remainder, KernelPrefix.identity⟩

def initialFloorMass (base childDepth : ℕ) (packed : ℕ × ℕ)
    (rows : List InitialAllocationRow) : ℕ × ℕ :=
  sumMassPairs ((List.range (childDepth + 2)).map fun zeros =>
    addMassPairs
      (if zeros = 0 then (0, 0) else
        scaleMassPair (rows[zeros]!).firstFalse
          (KernelPrefix.identity.rightOuter.action
            (packedGroupedFromRow base childDepth (zeros - 1) packed)))
      (scaleMassPair (rows[zeros]!).firstTrue
        (KernelPrefix.identity.rightCentral.action
          (packedGroupedFromRow base childDepth zeros packed))))

def initialMassEvaluation (depth : ℕ) (rows : List InitialAllocationRow) : ℕ × ℕ :=
  let base := matrixPackingBase depth
  let packed := packedInitialVector base depth
  let lexMass := runLexMassStream base depth packed ((base + 1) ^ depth)
    (initialLexStates depth rows)
  let floorMass := match depth with
    | 0 => scaleMassPair (rows[0]!).firstFalse (3139, 1313)
    | childDepth + 1 => initialFloorMass base childDepth (packedPreviousVector base packed) rows
  addMassPairs floorMass lexMass

end Universality.Certificates
