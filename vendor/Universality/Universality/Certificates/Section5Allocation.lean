import Universality.Certificates.Section5Packets
import Mathlib.Data.Nat.Choose.Basic

/-! The literal initial allocations used by the four Section 5 certificates. -/

namespace Universality.Certificates

/-- The binomial recurrence used for reduction by the kernel, rather than
the exponentially expanding Pascal recurrence. -/
def binomialByRatio (top : ℕ) : ℕ → ℕ
  | 0 => 1
  | index + 1 => binomialByRatio top index * (top - index) / (index + 1)

theorem binomialByRatio_eq_choose (top index : ℕ) :
    binomialByRatio top index = top.choose index := by
  induction index with
  | zero => simp [binomialByRatio]
  | succ index induction_hypothesis =>
      rw [binomialByRatio, induction_hypothesis, ← Nat.choose_succ_right_eq]
      exact Nat.mul_div_cancel _ (Nat.succ_pos _)

def firstZeroWordCount (depth zeros : ℕ) : ℕ :=
  if zeros = 0 then 0 else binomialByRatio (depth - 1) (zeros - 1)

/-- Zero-based rank among words of the same length and zero count, with
`false` preceding `true`. -/
def fixedZeroLexRank : List Bool → ℕ
  | [] => 0
  | false :: rest => fixedZeroLexRank rest
  | true :: rest =>
      firstZeroWordCount (rest.length + 1) (zeroCount rest) + fixedZeroLexRank rest

structure InitialAllocationRow where
  firstFalse : ℕ
  firstTrue : ℕ
  remainder : ℕ
  deriving Inhabited, DecidableEq

def initialAllocation (rows : List InitialAllocationRow) (word : List Bool) : ℕ :=
  (if word.headD false then (rows[zeroCount word]!).firstTrue
    else (rows[zeroCount word]!).firstFalse) +
    if fixedZeroLexRank word < (rows[zeroCount word]!).remainder then 1 else 0

def InitialAllocationRow.hasSlack (depth zeros slack : ℕ)
    (row : InitialAllocationRow) : Prop :=
  (0 < zeros → slack ≤ row.firstFalse ∧
    row.firstFalse + slack + (if 0 < row.remainder then 1 else 0) ≤ 2 ^ zeros) ∧
  (zeros < depth → slack ≤ row.firstTrue ∧
    row.firstTrue + slack +
      (if firstZeroWordCount depth zeros < row.remainder then 1 else 0) ≤ 2 ^ zeros)

instance (depth zeros slack : ℕ) (row : InitialAllocationRow) :
    Decidable (row.hasSlack depth zeros slack) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A slightly stronger certificate permits a remainder increment in either
first-letter class.  It avoids binomial reduction for the nonexceptional
capacity checks, without changing the allocation itself. -/
def InitialAllocationRow.hasUniformSlack (depth zeros slack : ℕ)
    (row : InitialAllocationRow) : Prop :=
  (0 < zeros → slack ≤ row.firstFalse ∧ row.firstFalse + slack + 1 ≤ 2 ^ zeros) ∧
  (zeros < depth → slack ≤ row.firstTrue ∧ row.firstTrue + slack + 1 ≤ 2 ^ zeros)

instance (depth zeros slack : ℕ) (row : InitialAllocationRow) :
    Decidable (row.hasUniformSlack depth zeros slack) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem InitialAllocationRow.hasSlack_of_uniform (row : InitialAllocationRow)
    (depth zeros slack : ℕ) (checked : row.hasUniformSlack depth zeros slack) :
    row.hasSlack depth zeros slack := by
  constructor
  · intro positive
    obtain ⟨lower, upper⟩ := checked.1 positive
    refine ⟨lower, ?_⟩
    split_ifs <;> omega
  · intro below_depth
    obtain ⟨lower, upper⟩ := checked.2 below_depth
    refine ⟨lower, ?_⟩
    split_ifs <;> omega

theorem zeroCount_le_length (word : List Bool) : zeroCount word ≤ word.length := by
  exact List.count_le_length

theorem initialAllocation_hasSlack (rows : List InitialAllocationRow)
    (word : List Bool) (slack : ℕ) (nonempty : word ≠ [])
    (checked : (rows[zeroCount word]!).hasSlack word.length (zeroCount word) slack) :
    slack ≤ initialAllocation rows word ∧
      initialAllocation rows word + slack ≤ 2 ^ zeroCount word := by
  cases word with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
      cases first
      · have lower_upper := checked.1 (by simp)
        simp only [initialAllocation, List.headD_cons, Bool.false_eq_true, ↓reduceIte]
        by_cases increment : fixedZeroLexRank (false :: rest) <
            (rows[zeroCount (false :: rest)]!).remainder
        · rw [if_pos increment]
          have positive : 0 < (rows[zeroCount (false :: rest)]!).remainder := by omega
          rw [if_pos positive] at lower_upper
          omega
        · rw [if_neg increment]
          split_ifs at lower_upper <;> omega
      · have zero_bound := zeroCount_le_length rest
        have lower_upper := checked.2 (by simpa using Nat.lt_succ_of_le zero_bound)
        simp only [initialAllocation, List.headD_cons, ↓reduceIte]
        by_cases increment : fixedZeroLexRank (true :: rest) <
            (rows[zeroCount (true :: rest)]!).remainder
        · rw [if_pos increment]
          have positive : firstZeroWordCount (true :: rest).length
              (zeroCount (true :: rest)) <
                (rows[zeroCount (true :: rest)]!).remainder := by
            simpa only [fixedZeroLexRank, List.length_cons, zeroCount_true_cons]
              using lt_of_le_of_lt (Nat.le_add_right _ _) increment
          rw [if_pos positive] at lower_upper
          omega
        · rw [if_neg increment]
          split_ifs at lower_upper <;> omega

structure CorrectionPacket where
  layer : ℕ
  first : Bool
  repeated : Bool
  remaining : ℕ
  coefficient : ℤ
  deriving Inhabited, DecidableEq

def CorrectionPacket.word (packet : CorrectionPacket) (choices : List Bool) : List Bool :=
  pairedWord choices ++ correctionTail packet.first packet.repeated packet.remaining

def CorrectionPacket.zeros (packet : CorrectionPacket) : ℕ :=
  (2 * packet.layer + 1) +
    zeroCount (correctionTail packet.first packet.repeated packet.remaining)

theorem CorrectionPacket.word_zeroCount (packet : CorrectionPacket) (choices : List Bool)
    (length_checked : choices.length = 2 * packet.layer + 1) :
    zeroCount (packet.word choices) = packet.zeros := by
  rw [CorrectionPacket.word, correction_fixed_zeroCount, length_checked]
  rfl

theorem CorrectionPacket.word_nonempty (packet : CorrectionPacket) (choices : List Bool) :
    packet.word choices ≠ [] := by
  simp [CorrectionPacket.word, correctionTail]

/-- The proof obligation for exceptional packets is a finite quantifier over
their (small) set of choices.  All other packets use the certified slack. -/
def CorrectionPacket.capacityChecked (rows : List InitialAllocationRow)
    (packet : CorrectionPacket) : Prop :=
  ∀ choices ∈ binaryWords (2 * packet.layer + 1),
    0 ≤ (initialAllocation rows (packet.word choices) : ℤ) +
      packet.coefficient * wordSign choices ∧
    (initialAllocation rows (packet.word choices) : ℤ) +
      packet.coefficient * wordSign choices ≤ 2 ^ packet.zeros

instance (rows : List InitialAllocationRow) (packet : CorrectionPacket) :
    Decidable (packet.capacityChecked rows) :=
  inferInstanceAs (Decidable (∀ choices ∈ binaryWords (2 * packet.layer + 1), _))

theorem CorrectionPacket.capacityChecked_of_slack (rows : List InitialAllocationRow)
    (packet : CorrectionPacket) (depth slack : ℕ)
    (length_checked : 2 * (2 * packet.layer + 1) + (packet.remaining + 2) = depth)
    (slack_checked : (rows[packet.zeros]!).hasSlack depth packet.zeros slack)
    (coefficient_checked : |packet.coefficient| ≤ (slack : ℤ)) :
    packet.capacityChecked rows := by
  intro choices member
  have choices_length := word_length_of_mem_binaryWords member
  have word_length : (packet.word choices).length = depth := by
    simpa [CorrectionPacket.word, List.length_append, pairedWord_length,
      choices_length, correctionTail_length] using length_checked
  have word_zeros := packet.word_zeroCount choices choices_length
  have initial_slack := initialAllocation_hasSlack rows (packet.word choices) slack
    (packet.word_nonempty choices) (by simpa only [word_length, word_zeros] using slack_checked)
  have signed_bounds := correction_capacity_of_slack
    (initialAllocation rows (packet.word choices)) (2 ^ packet.zeros) packet.coefficient slack
    choices (by exact_mod_cast initial_slack.1)
    (by exact_mod_cast (word_zeros ▸ initial_slack.2)) coefficient_checked
  exact signed_bounds

end Universality.Certificates
