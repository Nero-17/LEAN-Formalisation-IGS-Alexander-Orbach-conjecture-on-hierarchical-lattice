import Universality.Certificates.Section5BitExtraction

/-! Exact finite-chunk assembly used by production certificate endpoints.
Numerical checkpoints and their transition equalities are supplied separately.
This module proves generic assembly without asserting any concrete check. -/

namespace Universality.Certificates

structure LexMassCheckpoint where
  depth : ℕ
  packed : ℕ × ℕ
  packedCounts : ℕ
  states : List LexMassState
  mass : ℕ × ℕ
  deriving Inhabited, DecidableEq

def LexMassCheckpoint.step (bits : ℕ) (checkpoint : LexMassCheckpoint) : LexMassCheckpoint :=
  match checkpoint.depth with
  | 0 => checkpoint
  | childDepth + 1 =>
      let childPacked := packedPreviousVector (2 ^ bits) checkpoint.packed
      let childCounts := checkpoint.packedCounts / (2 ^ bits + 1)
      let next := advanceLexStates
        (fun zeros => packedGroupedBits bits childDepth zeros childPacked)
        (fun zeros => packedBinomialBits bits childDepth zeros childCounts) checkpoint.states
      ⟨childDepth, childPacked, childCounts, next.2, addMassPairs checkpoint.mass next.1⟩

def runLexMassChunk (bits : ℕ) : ℕ → LexMassCheckpoint → LexMassCheckpoint
  | 0, checkpoint => checkpoint
  | steps + 1, checkpoint => runLexMassChunk bits steps (checkpoint.step bits)

def LexMassCheckpoint.value (bits : ℕ) (checkpoint : LexMassCheckpoint) : ℕ × ℕ :=
  addMassPairs checkpoint.mass
    (runLexMassBitStream bits checkpoint.depth checkpoint.packed checkpoint.packedCounts checkpoint.states)

theorem addMassPairs_assoc (first second third : ℕ × ℕ) :
    addMassPairs (addMassPairs first second) third =
      addMassPairs first (addMassPairs second third) := by
  apply Prod.ext <;> simp [addMassPairs, Nat.add_assoc]

theorem LexMassCheckpoint.step_value (bits : ℕ) (checkpoint : LexMassCheckpoint) :
    (checkpoint.step bits).value bits = checkpoint.value bits := by
  rcases checkpoint with ⟨depth, packed, packedCounts, states, mass⟩
  cases depth with
  | zero => rfl
  | succ depth =>
      simp only [LexMassCheckpoint.step, LexMassCheckpoint.value, runLexMassBitStream]
      exact addMassPairs_assoc _ _ _

theorem LexMassCheckpoint.step_depth (bits : ℕ) (checkpoint : LexMassCheckpoint) :
    (checkpoint.step bits).depth = checkpoint.depth - 1 := by
  rcases checkpoint with ⟨depth, packed, packedCounts, states, mass⟩
  cases depth <;> rfl

theorem runLexMassChunk_value (bits steps : ℕ) (checkpoint : LexMassCheckpoint) :
    (runLexMassChunk bits steps checkpoint).value bits = checkpoint.value bits := by
  induction steps generalizing checkpoint with
  | zero => rfl
  | succ steps ih =>
      rw [runLexMassChunk, ih, LexMassCheckpoint.step_value]

theorem runLexMassChunk_depth (bits steps : ℕ) (checkpoint : LexMassCheckpoint) :
    (runLexMassChunk bits steps checkpoint).depth = checkpoint.depth - steps := by
  induction steps generalizing checkpoint with
  | zero => simp [runLexMassChunk]
  | succ steps ih =>
      rw [runLexMassChunk, ih, LexMassCheckpoint.step_depth]
      omega

theorem runLexMassChunk_add (bits firstSteps secondSteps : ℕ)
    (checkpoint : LexMassCheckpoint) :
    runLexMassChunk bits (firstSteps + secondSteps) checkpoint =
      runLexMassChunk bits secondSteps (runLexMassChunk bits firstSteps checkpoint) := by
  induction firstSteps generalizing checkpoint with
  | zero => simp [runLexMassChunk]
  | succ firstSteps ih =>
      simp only [Nat.succ_add, runLexMassChunk, ih]

theorem runLexMassChunk_witnesses (bits firstSteps secondSteps : ℕ)
    (first middle last : LexMassCheckpoint)
    (first_checked : runLexMassChunk bits firstSteps first = middle)
    (second_checked : runLexMassChunk bits secondSteps middle = last) :
    runLexMassChunk bits (firstSteps + secondSteps) first = last := by
  rw [runLexMassChunk_add, first_checked, second_checked]

/-- Adjacent chunks may be composed as value equalities, without ever asking
the kernel to reduce the concatenated run again. -/
theorem runLexMassChunk_value_of_check (bits steps : ℕ)
    (first last : LexMassCheckpoint)
    (checked : runLexMassChunk bits steps first = last) :
    first.value bits = last.value bits := by
  rw [← checked, runLexMassChunk_value]

def initialFloorFromPackedBits (bits depth : ℕ) (rows : List InitialAllocationRow)
    (packed : ℕ × ℕ) : ℕ × ℕ :=
  match depth with
  | 0 => scaleMassPair (rows[0]!).firstFalse (3139, 1313)
  | childDepth + 1 => initialFloorMassBits bits childDepth
      (packedPreviousVector (2 ^ bits) packed) rows

theorem initialMassEvaluationBits_split (depth : ℕ) (rows : List InitialAllocationRow) :
    initialMassEvaluationBits depth rows =
      addMassPairs
        (initialFloorFromPackedBits (6 * (depth + 1) + 12) depth rows
          (packedInitialVector (matrixPackingBase depth) depth))
        (runLexMassBitStream (6 * (depth + 1) + 12) depth
          (packedInitialVector (matrixPackingBase depth) depth)
          ((matrixPackingBase depth + 1) ^ depth) (initialLexStates depth rows)) := by
  rfl

/-- The complete original evaluator follows from bounded transition checks,
the actual initial packed data, the actual floor computation, and the terminal
mass. No intermediate numerical result is accepted without an equality proof. -/
theorem initialMassEvaluation_of_chunk_values (depth : ℕ)
    (rows : List InitialAllocationRow) (first last : LexMassCheckpoint)
    (floor result : ℕ × ℕ)
    (initial_depth : first.depth = depth)
    (initial_packed : first.packed = packedInitialVector (matrixPackingBase depth) depth)
    (initial_counts : first.packedCounts = (matrixPackingBase depth + 1) ^ depth)
    (initial_states : first.states = initialLexStates depth rows)
    (initial_mass : first.mass = (0, 0))
    (chain_checked : first.value (6 * (depth + 1) + 12) = last.value (6 * (depth + 1) + 12))
    (terminal_depth : last.depth = 0)
    (floor_checked : initialFloorFromPackedBits (6 * (depth + 1) + 12)
      depth rows first.packed = floor)
    (terminal_checked : addMassPairs floor
      (addMassPairs last.mass (sumMassPairs (last.states.map terminalLexMass))) = result) :
    initialMassEvaluation depth rows = result := by
  have stream_checked :
      runLexMassBitStream (6 * (depth + 1) + 12) depth
        (packedInitialVector (matrixPackingBase depth) depth)
        ((matrixPackingBase depth + 1) ^ depth) (initialLexStates depth rows) =
      addMassPairs last.mass (sumMassPairs (last.states.map terminalLexMass)) := by
    unfold LexMassCheckpoint.value at chain_checked
    rw [initial_depth, initial_packed, initial_counts, initial_states, initial_mass,
      terminal_depth, runLexMassBitStream] at chain_checked
    simpa only [addMassPairs, Nat.zero_add, Prod.mk.eta] using chain_checked
  rw [← initialMassEvaluationBits_eq, initialMassEvaluationBits_split, stream_checked]
  rw [initial_packed] at floor_checked
  rw [floor_checked]
  exact terminal_checked

theorem runLexMassBitStream_of_chunk_witness (bits depth steps : ℕ)
    (packed : ℕ × ℕ) (packedCounts : ℕ) (states : List LexMassState)
    (last : LexMassCheckpoint) (result : ℕ × ℕ)
    (checked : runLexMassChunk bits steps ⟨depth, packed, packedCounts, states, (0, 0)⟩ = last)
    (finished : last.depth = 0)
    (terminal_checked : addMassPairs last.mass (sumMassPairs (last.states.map terminalLexMass)) = result) :
    runLexMassBitStream bits depth packed packedCounts states = result := by
  have invariant := runLexMassChunk_value bits steps
    (⟨depth, packed, packedCounts, states, (0, 0)⟩ : LexMassCheckpoint)
  rw [checked] at invariant
  unfold LexMassCheckpoint.value at invariant
  rw [finished, runLexMassBitStream, terminal_checked] at invariant
  simpa only [addMassPairs, Nat.zero_add, Prod.mk.eta] using invariant.symm

#print axioms runLexMassChunk_witnesses
#print axioms runLexMassBitStream_of_chunk_witness
#print axioms initialMassEvaluation_of_chunk_values

end Universality.Certificates
