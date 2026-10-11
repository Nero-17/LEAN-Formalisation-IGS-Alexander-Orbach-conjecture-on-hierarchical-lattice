import Universality.Certificates.Section5MatrixStream

set_option backward.isDefEq.respectTransparency false

/-! Exact ordered invariants for the simultaneous streaming evaluator. -/

namespace Universality.Certificates
open Matrix

def massPairVector (pair : ℕ × ℕ) : Fin 2 → ℕ := ![pair.1, pair.2]

@[simp] theorem massPairVector_initial : massPairVector (3139, 1313) = initialMassVector := rfl

@[simp] theorem massPairVector_zero : massPairVector (0, 0) = 0 := by
  ext index
  fin_cases index <;> rfl

@[simp] theorem massPairVector_add (first second : ℕ × ℕ) :
    massPairVector (addMassPairs first second) = massPairVector first + massPairVector second := by
  ext index
  fin_cases index <;> rfl

@[simp] theorem massPairVector_scale (coefficient : ℕ) (pair : ℕ × ℕ) :
    massPairVector (scaleMassPair coefficient pair) = coefficient • massPairVector pair := by
  ext index
  fin_cases index <;> rfl

@[simp] theorem massPairVector_sum (pairs : List (ℕ × ℕ)) :
    massPairVector (sumMassPairs pairs) = (pairs.map massPairVector).sum := by
  induction pairs with
  | nil => simp [sumMassPairs]
  | cons pair pairs induction_hypothesis => simp [sumMassPairs, induction_hypothesis]

@[simp] theorem KernelPrefix.identity_toMatrix : KernelPrefix.identity.toMatrix = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;> rfl

@[simp] theorem KernelPrefix.rightOuter_toMatrix (accumulated : KernelPrefix) :
    accumulated.rightOuter.toMatrix = accumulated.toMatrix * naturalOuterKernel := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [KernelPrefix.rightOuter, KernelPrefix.toMatrix, naturalOuterKernel,
      Matrix.mul_apply, Fin.sum_univ_two, Nat.mul_comm]

@[simp] theorem KernelPrefix.rightCentral_toMatrix (accumulated : KernelPrefix) :
    accumulated.rightCentral.toMatrix = accumulated.toMatrix * naturalCentralKernel := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [KernelPrefix.rightCentral, KernelPrefix.toMatrix, naturalCentralKernel,
      Matrix.mul_apply, Fin.sum_univ_two, Nat.mul_comm]

@[simp] theorem KernelPrefix.action_vector (accumulated : KernelPrefix) (pair : ℕ × ℕ) :
    massPairVector (accumulated.action pair) = accumulated.toMatrix *ᵥ massPairVector pair := by
  ext index
  fin_cases index <;>
    simp [massPairVector, KernelPrefix.action, KernelPrefix.toMatrix,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two]

def LexMassState.exactMass (state : LexMassState) (depth : ℕ) : Fin 2 → ℕ :=
  state.accumulated.toMatrix *ᵥ
    (lexPrefixWordSum naturalOuterKernel naturalCentralKernel depth
      state.remainingZeros state.remainder *ᵥ initialMassVector)

/-- Splitting a lexicographic prefix retains the root-to-leaf matrix order. -/
theorem lexPrefixWordSum_step_action (depth zeros cutoff : ℕ)
    (prefixMatrix : Matrix (Fin 2) (Fin 2) ℕ) :
    prefixMatrix *ᵥ (lexPrefixWordSum naturalOuterKernel naturalCentralKernel
        (depth + 1) zeros cutoff *ᵥ initialMassVector) =
      if cutoff = 0 then 0 else
        if cutoff ≤ firstZeroWordCount (depth + 1) zeros then
          (prefixMatrix * naturalOuterKernel) *ᵥ
            (lexPrefixWordSum naturalOuterKernel naturalCentralKernel
              depth (zeros - 1) cutoff *ᵥ initialMassVector)
        else
          (if zeros = 0 then 0 else
            (prefixMatrix * naturalOuterKernel) *ᵥ groupedMassVector depth (zeros - 1)) +
          (prefixMatrix * naturalCentralKernel) *ᵥ
            (lexPrefixWordSum naturalOuterKernel naturalCentralKernel depth zeros
              (cutoff - firstZeroWordCount (depth + 1) zeros) *ᵥ initialMassVector) := by
  by_cases empty : cutoff = 0
  · simp [empty, lexPrefixWordSum_cutoff_zero]
  · cases zeros with
    | zero =>
        simp [empty, firstZeroWordCount, lexPrefixWordSum_succ_zero,
          ← Matrix.mulVec_mulVec]
    | succ zeros =>
        rw [lexPrefixWordSum_split]
        by_cases first_block : cutoff ≤ depth.choose zeros
        · simp [empty, firstZeroWordCount, binomialByRatio_eq_choose, first_block,
            ← Matrix.mulVec_mulVec]
        · simp [empty, firstZeroWordCount, binomialByRatio_eq_choose, first_block,
            Matrix.add_mulVec, Matrix.mulVec_add, ← Matrix.mulVec_mulVec,
            groupedMassVector]

theorem advanceLexState_correct (depth : ℕ)
    (grouped : ℕ → ℕ × ℕ) (counts : ℕ → ℕ)
    (grouped_correct : ∀ zeros, massPairVector (grouped zeros) = groupedMassVector depth zeros)
    (counts_correct : ∀ zeros, counts zeros = depth.choose zeros)
    (state : LexMassState) :
    state.exactMass (depth + 1) = massPairVector (advanceLexState grouped counts state).1 +
      (advanceLexState grouped counts state).2.exactMass depth := by
  rcases state with ⟨zeros, cutoff, accumulated⟩
  have recurrence := lexPrefixWordSum_step_action depth zeros cutoff accumulated.toMatrix
  by_cases empty : cutoff = 0
  · simp [advanceLexState, LexMassState.exactMass, empty, lexPrefixWordSum_cutoff_zero]
  · by_cases no_zeros : zeros = 0
    · simpa [advanceLexState, LexMassState.exactMass, empty, no_zeros,
        firstZeroWordCount, ← Matrix.mulVec_mulVec] using recurrence
    · by_cases first_block : cutoff ≤ depth.choose (zeros - 1)
      · simpa [advanceLexState, LexMassState.exactMass, empty, no_zeros,
          firstZeroWordCount, binomialByRatio_eq_choose, counts_correct, first_block,
          ← Matrix.mulVec_mulVec] using recurrence
      · simpa [advanceLexState, LexMassState.exactMass, empty, no_zeros,
          firstZeroWordCount, binomialByRatio_eq_choose, counts_correct, first_block,
          grouped_correct, ← Matrix.mulVec_mulVec] using recurrence

theorem advanceLexStates_correct (depth : ℕ)
    (grouped : ℕ → ℕ × ℕ) (counts : ℕ → ℕ)
    (grouped_correct : ∀ zeros, massPairVector (grouped zeros) = groupedMassVector depth zeros)
    (counts_correct : ∀ zeros, counts zeros = depth.choose zeros)
    (states : List LexMassState) :
    (states.map (fun state => state.exactMass (depth + 1))).sum =
      massPairVector (advanceLexStates grouped counts states).1 +
        ((advanceLexStates grouped counts states).2.map (fun state => state.exactMass depth)).sum := by
  induction states with
  | nil => simp [advanceLexStates]
  | cons state states induction_hypothesis =>
      simp only [List.map_cons, List.sum_cons, advanceLexStates]
      rw [advanceLexState_correct depth grouped counts grouped_correct counts_correct state,
        induction_hypothesis, massPairVector_add]
      simp [add_assoc, add_left_comm]

theorem terminalLexMass_correct (state : LexMassState) :
    massPairVector (terminalLexMass state) = state.exactMass 0 := by
  unfold terminalLexMass LexMassState.exactMass
  rw [lexPrefixWordSum_depth_zero]
  by_cases terminal : state.remainingZeros = 0 ∧ 0 < state.remainder
  · simpa only [if_pos terminal, Matrix.one_mulVec, massPairVector_initial] using
      KernelPrefix.action_vector state.accumulated (3139, 1313)
  · simp [terminal]

/-- A whole descending run preserves the sum of all unfinished lexicographic prefixes. -/
theorem runLexMassStream_correct (maximum depth : ℕ) (valid : depth ≤ maximum)
    (states : List LexMassState) :
    massPairVector (runLexMassStream (matrixPackingBase maximum) depth
      (packedInitialVector (matrixPackingBase maximum) depth)
      ((matrixPackingBase maximum + 1) ^ depth) states) =
        (states.map (fun state => state.exactMass depth)).sum := by
  induction depth generalizing states with
  | zero =>
      simp only [runLexMassStream, massPairVector_sum, List.map_map,
        Function.comp_def, terminalLexMass_correct]
  | succ depth induction_hypothesis =>
      have child_valid : depth ≤ maximum := by omega
      simp only [runLexMassStream, packedPreviousVector_correct, packedBinomial_previous,
        massPairVector_add]
      rw [induction_hypothesis child_valid]
      exact (advanceLexStates_correct depth _ _
        (fun zeros => packedGroupedFromRow_correct maximum depth zeros child_valid)
        (fun zeros => packedBinomialFromRow_correct maximum depth zeros child_valid) states).symm

theorem initialLexStates_mass (depth : ℕ) (rows : List InitialAllocationRow) :
    ((initialLexStates depth rows).map (fun state => state.exactMass depth)).sum =
      ((List.range (depth + 1)).map (fun zeros =>
        lexPrefixWordSum naturalOuterKernel naturalCentralKernel depth zeros
          (rows[zeros]!).remainder *ᵥ initialMassVector)).sum := by
  simp [initialLexStates, List.map_map, Function.comp_def, LexMassState.exactMass]

theorem initialFloorMass_correct (maximum depth : ℕ) (valid : depth ≤ maximum)
    (rows : List InitialAllocationRow) :
    massPairVector (initialFloorMass (matrixPackingBase maximum) depth
      (packedInitialVector (matrixPackingBase maximum) depth) rows) =
        ((List.range (depth + 2)).map (fun zeros =>
          (if zeros = 0 then (0 : Fin 2 → ℕ) else (rows[zeros]!).firstFalse •
            (naturalOuterKernel *ᵥ groupedMassVector depth (zeros - 1))) +
          (rows[zeros]!).firstTrue •
            (naturalCentralKernel *ᵥ groupedMassVector depth zeros))).sum := by
  simp only [initialFloorMass, massPairVector_sum, List.map_map, Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro zeros _
  have grouped (index : ℕ) : massPairVector
      (packedGroupedFromRow (matrixPackingBase maximum) depth index
        (packedInitialVector (matrixPackingBase maximum) depth)) = groupedMassVector depth index :=
    packedGroupedFromRow_correct maximum depth index valid
  by_cases no_zeros : zeros = 0
  · simp [no_zeros, grouped]
  · simp [no_zeros, grouped]

theorem matrix_sum_action_list {α : Type*} (items : List α)
    (matrix : α → Matrix (Fin 2) (Fin 2) ℕ) (vector : Fin 2 → ℕ) :
    (items.map matrix).sum *ᵥ vector = (items.map (fun item => matrix item *ᵥ vector)).sum := by
  induction items with
  | nil => simp
  | cons item items induction_hypothesis =>
      simp only [List.map_cons, List.sum_cons, Matrix.add_mulVec, induction_hypothesis]

/-- Exact natural ordered mass sum; this is an evaluation theorem, not a numerical certificate. -/
theorem initialMassEvaluation_correct (depth : ℕ) (rows : List InitialAllocationRow) :
    massPairVector (initialMassEvaluation depth rows) =
      ((binaryWords depth).map (fun word => initialAllocation rows word •
        wordProduct naturalOuterKernel naturalCentralKernel word)).sum *ᵥ initialMassVector := by
  simp only [nsmul_eq_mul]
  cases depth with
  | zero =>
      simp only [initialMassEvaluation, massPairVector_add, massPairVector_scale]
      rw [runLexMassStream_correct 0 0 (by omega), initialLexStates_mass]
      simp [massPairVector_initial, lexPrefixWordSum_depth_zero, binaryWords, wordProduct,
        initialAllocation, fixedZeroLexRank, zeroCount, Matrix.add_mulVec,
        Matrix.natCast_mulVec, nsmul_eq_mul]
  | succ depth =>
      simp only [initialMassEvaluation, packedPreviousVector_correct, massPairVector_add]
      rw [initialFloorMass_correct (depth + 1) depth (by omega),
        runLexMassStream_correct (depth + 1) (depth + 1) (by omega), initialLexStates_mass,
        initialAllocation_ordered_word_sum, matrix_sum_action_list, ← List.sum_map_add]
      apply congrArg List.sum
      apply List.map_congr_left
      intro zeros _
      by_cases no_zeros : zeros = 0
      · simp [no_zeros, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.natCast_mulVec,
          groupedMassVector]
      · simp [no_zeros, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.natCast_mulVec,
          groupedMassVector]

#print axioms runLexMassStream_correct
#print axioms initialMassEvaluation_correct

end Universality.Certificates
