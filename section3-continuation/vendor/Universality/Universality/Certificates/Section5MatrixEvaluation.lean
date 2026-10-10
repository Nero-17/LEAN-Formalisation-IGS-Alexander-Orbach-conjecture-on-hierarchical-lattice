import Universality.Certificates.Section5InitialSums
import Mathlib.Data.Nat.Digits.Lemmas
import Universality.Certificates.Capacity
import Mathlib.Data.Nat.Choose.Bounds

/-! Proof-producing numerical evaluation for Section 5. Native execution is
not used as proof. The initial benchmark declarations test ordinary kernel
reduction before the large-data evaluator is selected. -/

namespace Universality.Certificates
open Matrix

def packedInitialVector (base : ℕ) : ℕ → ℕ × ℕ
  | 0 => (3139, 1313)
  | depth + 1 =>
      let previous := packedInitialVector base depth
      ((22 * base + 9) * previous.1 + (18 * base + 12) * previous.2,
       (5 * base + 3) * previous.1 + (18 * base + 6) * previous.2)

def matrixPackingBase (depth : ℕ) : ℕ := 2 ^ (6 * (depth + 1) + 12)

/-- Exact extraction requires a bound on every coefficient; no carry is assumed
silently. This is the arithmetic boundary used by packed evaluation. -/
theorem packed_digit_extract (base index : ℕ) (digits : List ℕ)
    (positive : 0 < base) (bounded : ∀ digit ∈ digits, digit < base) :
    Nat.ofDigits base digits / base ^ index % base = (digits.drop index).head! := by
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop index positive digits bounded,
    Nat.ofDigits_mod_eq_head!]
  apply Nat.mod_eq_of_lt
  cases dropped : digits.drop index with
  | nil => simpa [dropped] using positive
  | cons head tail =>
      simp only [List.head!_cons]
      apply bounded
      apply List.mem_of_mem_drop (i := index)
      simp [dropped]

theorem packedInitialVector_one_bound (depth : ℕ) :
    (packedInitialVector 1 depth).1 ≤ 3139 * 61 ^ depth ∧
      (packedInitialVector 1 depth).2 ≤ 3139 * 61 ^ depth := by
  induction depth with
  | zero => norm_num [packedInitialVector]
  | succ depth ih =>
      simp only [packedInitialVector, Nat.pow_succ]
      constructor <;> nlinarith [ih.1, ih.2]

def naturalOuterKernel : Matrix (Fin 2) (Fin 2) ℕ := !![22, 18; 5, 18]
def naturalCentralKernel : Matrix (Fin 2) (Fin 2) ℕ := !![9, 12; 3, 6]
def initialMassVector : Fin 2 → ℕ := ![3139, 1313]

theorem packedInitialVector_eq_matrix (base depth : ℕ) :
    ![(packedInitialVector base depth).1, (packedInitialVector base depth).2] =
      (base • naturalOuterKernel + naturalCentralKernel) ^ depth *ᵥ initialMassVector := by
  induction depth with
  | zero => simp [packedInitialVector, initialMassVector]
  | succ depth ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih]
      ext index
      fin_cases index <;>
        simp [packedInitialVector, naturalOuterKernel, naturalCentralKernel,
          Matrix.mulVec, dotProduct, Fin.sum_univ_two, Nat.mul_comm]

theorem packed_grouped_matrix_sum {R : Type*} [Semiring R]
    (outer central : R) (base depth : ℕ) :
    ((List.range (depth + 1)).map (fun zeros =>
      base ^ zeros • groupedWordSum outer central depth zeros)).sum =
      (base • outer + central) ^ depth := by
  rw [← weighted_word_sum, sum_grouped_zeroCount]
  apply congrArg List.sum
  apply List.map_congr_left
  intro zeros _
  rw [← fixedZeroWords_word_sum, List.smul_sum, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro word member
  rw [(mem_fixedZeroWords member).2]
  rfl

def groupedMassVector (depth zeros : ℕ) : Fin 2 → ℕ :=
  groupedWordSum naturalOuterKernel naturalCentralKernel depth zeros *ᵥ initialMassVector

theorem groupedMassVector_bound (depth zeros : ℕ) :
    groupedMassVector depth zeros 0 ≤ 3139 * 61 ^ depth ∧
      groupedMassVector depth zeros 1 ≤ 3139 * 61 ^ depth := by
  induction depth generalizing zeros with
  | zero =>
      simp only [groupedMassVector, groupedWordSum_zero]
      split_ifs <;> norm_num [initialMassVector]
  | succ depth ih =>
      cases zeros with
      | zero =>
          have bounds := ih 0
          simp only [groupedMassVector, groupedWordSum_succ_zero,
            ← Matrix.mulVec_mulVec, Nat.pow_succ]
          change 9 * groupedMassVector depth 0 0 + 12 * groupedMassVector depth 0 1 ≤ _ ∧
            3 * groupedMassVector depth 0 0 + 6 * groupedMassVector depth 0 1 ≤ _
          constructor <;> nlinarith [bounds.1, bounds.2]
      | succ zeros =>
          have first := ih zeros
          have second := ih (zeros + 1)
          simp only [groupedMassVector, groupedWordSum_succ_succ, Matrix.add_mulVec,
            ← Matrix.mulVec_mulVec, Nat.pow_succ]
          change (22 * groupedMassVector depth zeros 0 + 18 * groupedMassVector depth zeros 1) +
            (9 * groupedMassVector depth (zeros + 1) 0 + 12 * groupedMassVector depth (zeros + 1) 1) ≤ _ ∧
            (5 * groupedMassVector depth zeros 0 + 18 * groupedMassVector depth zeros 1) +
            (3 * groupedMassVector depth (zeros + 1) 0 + 6 * groupedMassVector depth (zeros + 1) 1) ≤ _
          constructor <;> nlinarith [first.1, first.2, second.1, second.2]

theorem matrixPackingBase_bound (depth : ℕ) :
    3139 * 61 ^ depth < matrixPackingBase depth := by
  have comparison : 61 ^ depth ≤ 64 ^ depth := Nat.pow_le_pow_left (by decide : 61 ≤ 64) depth
  have positive : 0 < 64 ^ depth := pow_pos (by decide) _
  unfold matrixPackingBase
  rw [show 6 * (depth + 1) + 12 = 6 * depth + 18 by omega, pow_add, pow_mul]
  norm_num
  nlinarith

theorem ofDigits_map_range (base length : ℕ) (coefficient : ℕ → ℕ) :
    Nat.ofDigits base ((List.range length).map coefficient) =
      ((List.range length).map (fun index => coefficient index * base ^ index)).sum := by
  induction length with
  | zero => simp
  | succ length ih =>
      simp [List.range_succ, Nat.ofDigits_append, ih, Nat.mul_comm]

theorem list_sum_mulVec_apply {α : Type*} (items : List α)
    (matrix : α → Matrix (Fin 2) (Fin 2) ℕ) (vector : Fin 2 → ℕ) (index : Fin 2) :
    ((items.map matrix).sum *ᵥ vector) index =
      (items.map (fun item => (matrix item *ᵥ vector) index)).sum := by
  induction items with
  | nil => simp
  | cons item items ih => simp [Matrix.add_mulVec, ih]

theorem packedInitialVector_eq_ofDigits (base depth : ℕ) (index : Fin 2) :
    ![(packedInitialVector base depth).1, (packedInitialVector base depth).2] index =
      Nat.ofDigits base ((List.range (depth + 1)).map (fun zeros => groupedMassVector depth zeros index)) := by
  rw [packedInitialVector_eq_matrix, ← packed_grouped_matrix_sum,
    list_sum_mulVec_apply, ofDigits_map_range]
  apply congrArg List.sum
  apply List.map_congr_left
  intro zeros _
  rw [Matrix.smul_mulVec]
  simp only [Pi.smul_apply, smul_eq_mul, groupedMassVector, Nat.mul_comm]

theorem packedInitialVector_extract_of_bound (base depth zeros : ℕ) (index : Fin 2)
    (large : 3139 * 61 ^ depth < base) (valid : zeros ≤ depth) :
    ![(packedInitialVector base depth).1, (packedInitialVector base depth).2] index /
        base ^ zeros % base = groupedMassVector depth zeros index := by
  rw [packedInitialVector_eq_ofDigits]
  have positive : 0 < base := lt_of_le_of_lt (Nat.zero_le _) large
  rw [packed_digit_extract _ _ _ positive]
  · simp [List.head!_eq_getElem!, show zeros < depth + 1 by omega]
  · intro digit member
    obtain ⟨other, _, rfl⟩ := List.mem_map.mp member
    have bound := groupedMassVector_bound depth other
    have index_bound : groupedMassVector depth other index ≤ 3139 * 61 ^ depth := by
      fin_cases index
      · exact bound.1
      · exact bound.2
    exact lt_of_le_of_lt index_bound large

theorem packedInitialVector_extract (depth zeros : ℕ) (index : Fin 2)
    (valid : zeros ≤ depth) :
    ![(packedInitialVector (matrixPackingBase depth) depth).1,
      (packedInitialVector (matrixPackingBase depth) depth).2] index /
        matrixPackingBase depth ^ zeros % matrixPackingBase depth =
      groupedMassVector depth zeros index :=
  packedInitialVector_extract_of_bound _ _ _ _ (matrixPackingBase_bound depth) valid

theorem matrixPackingBase_global_bound (maximum depth : ℕ) (valid : depth ≤ maximum) :
    3139 * 61 ^ depth < matrixPackingBase maximum := by
  apply lt_of_le_of_lt _ (matrixPackingBase_bound maximum)
  exact Nat.mul_le_mul_left 3139 (Nat.pow_le_pow_right (by decide : 0 < 61) valid)

theorem groupedMassVector_above_depth (depth zeros : ℕ) (invalid : depth < zeros) :
    groupedMassVector depth zeros = 0 := by
  unfold groupedMassVector groupedWordSum
  have zero_terms : (binaryWords depth).map
      (fun word => if zeroCount word = zeros then wordProduct naturalOuterKernel naturalCentralKernel word else 0) =
      (binaryWords depth).map (fun _ => (0 : Matrix (Fin 2) (Fin 2) ℕ)) := by
    apply List.map_congr_left
    intro word member
    have word_length := word_length_of_mem_binaryWords member
    have zero_bound := zeroCount_le_length word
    simp [show zeroCount word ≠ zeros by omega]
  rw [zero_terms]
  simp

def packedGroupedVector (base depth zeros : ℕ) : ℕ × ℕ :=
  if zeros ≤ depth then
    let packed := packedInitialVector base depth
    (packed.1 / base ^ zeros % base, packed.2 / base ^ zeros % base)
  else (0, 0)

theorem packedGroupedVector_correct (maximum depth zeros : ℕ) (valid : depth ≤ maximum) :
    ![(packedGroupedVector (matrixPackingBase maximum) depth zeros).1,
      (packedGroupedVector (matrixPackingBase maximum) depth zeros).2] =
      groupedMassVector depth zeros := by
  by_cases in_range : zeros ≤ depth
  · ext index
    fin_cases index <;> simp only [packedGroupedVector, if_pos in_range, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons]
    · exact packedInitialVector_extract_of_bound _ _ _ 0
        (matrixPackingBase_global_bound maximum depth valid) in_range
    · exact packedInitialVector_extract_of_bound _ _ _ 1
        (matrixPackingBase_global_bound maximum depth valid) in_range
  · rw [groupedMassVector_above_depth depth zeros (by omega)]
    simp [packedGroupedVector, in_range]

#print axioms packedInitialVector_extract
#print axioms packedGroupedVector_correct

def packedStepDeterminant (base : ℕ) : ℕ := 306 * base ^ 2 + 180 * base + 18

def packedPreviousVector (base : ℕ) (next : ℕ × ℕ) : ℕ × ℕ :=
  (((18 * base + 6) * next.1 - (18 * base + 12) * next.2) / packedStepDeterminant base,
   ((22 * base + 9) * next.2 - (5 * base + 3) * next.1) / packedStepDeterminant base)

theorem packedPreviousVector_correct (base depth : ℕ) :
    packedPreviousVector base (packedInitialVector base (depth + 1)) =
      packedInitialVector base depth := by
  have positive : 0 < packedStepDeterminant base := by
    unfold packedStepDeterminant
    omega
  have first_identity :
      (18 * base + 6) * (packedInitialVector base (depth + 1)).1 =
        (18 * base + 12) * (packedInitialVector base (depth + 1)).2 +
          packedStepDeterminant base * (packedInitialVector base depth).1 := by
    simp only [packedInitialVector, packedStepDeterminant]
    ring
  have second_identity :
      (22 * base + 9) * (packedInitialVector base (depth + 1)).2 =
        (5 * base + 3) * (packedInitialVector base (depth + 1)).1 +
          packedStepDeterminant base * (packedInitialVector base depth).2 := by
    simp only [packedInitialVector, packedStepDeterminant]
    ring
  apply Prod.ext
  · change (_ - _) / _ = _
    rw [first_identity, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ positive]
  · change (_ - _) / _ = _
    rw [second_identity, Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ positive]

#print axioms packedPreviousVector_correct

def packedGroupedFromRow (base depth zeros : ℕ) (packed : ℕ × ℕ) : ℕ × ℕ :=
  if zeros ≤ depth then
    (packed.1 / base ^ zeros % base, packed.2 / base ^ zeros % base)
  else (0, 0)

theorem packedGroupedFromRow_correct (maximum depth zeros : ℕ)
    (valid : depth ≤ maximum) :
    ![(packedGroupedFromRow (matrixPackingBase maximum) depth zeros
        (packedInitialVector (matrixPackingBase maximum) depth)).1,
      (packedGroupedFromRow (matrixPackingBase maximum) depth zeros
        (packedInitialVector (matrixPackingBase maximum) depth)).2] =
      groupedMassVector depth zeros :=
  packedGroupedVector_correct maximum depth zeros valid

theorem packedBinomial_eq_ofDigits (base depth : ℕ) :
    (base + 1) ^ depth = Nat.ofDigits base
      ((List.range (depth + 1)).map (fun zeros => depth.choose zeros)) := by
  rw [ofDigits_map_range]
  have identity := packed_grouped_matrix_sum (1 : ℕ) 1 base depth
  simpa only [binary_group_cardinality, nsmul_eq_mul, Nat.cast_id, mul_one, Nat.mul_comm] using identity.symm

theorem packedBinomial_extract (maximum depth zeros : ℕ)
    (valid : depth ≤ maximum) (in_range : zeros ≤ depth) :
    (matrixPackingBase maximum + 1) ^ depth /
      matrixPackingBase maximum ^ zeros % matrixPackingBase maximum = depth.choose zeros := by
  rw [packedBinomial_eq_ofDigits]
  have positive : 0 < matrixPackingBase maximum :=
    lt_of_le_of_lt (Nat.zero_le _) (matrixPackingBase_bound maximum)
  rw [packed_digit_extract _ _ _ positive]
  · simp [List.head!_eq_getElem!, show zeros < depth + 1 by omega]
  · intro digit member
    obtain ⟨other, _, rfl⟩ := List.mem_map.mp member
    have bound := Nat.choose_le_two_pow depth other
    have comparison : 2 ^ depth ≤ 61 ^ depth := Nat.pow_le_pow_left (by decide : 2 ≤ 61) depth
    have large := matrixPackingBase_global_bound maximum depth valid
    omega

def packedBinomialFromRow (base depth zeros packed : ℕ) : ℕ :=
  if zeros ≤ depth then packed / base ^ zeros % base else 0

theorem packedBinomialFromRow_correct (maximum depth zeros : ℕ) (valid : depth ≤ maximum) :
    packedBinomialFromRow (matrixPackingBase maximum) depth zeros
      ((matrixPackingBase maximum + 1) ^ depth) = depth.choose zeros := by
  by_cases in_range : zeros ≤ depth
  · exact (if_pos in_range).trans (packedBinomial_extract maximum depth zeros valid in_range)
  · simp [packedBinomialFromRow, in_range, Nat.choose_eq_zero_of_lt (by omega : depth < zeros)]

theorem packedBinomial_previous (base depth : ℕ) :
    (base + 1) ^ (depth + 1) / (base + 1) = (base + 1) ^ depth := by
  rw [pow_succ, Nat.mul_div_cancel _ (by omega : 0 < base + 1)]

#print axioms packedBinomialFromRow_correct

end Universality.Certificates


