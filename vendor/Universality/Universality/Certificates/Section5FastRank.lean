import Universality.Certificates.Section5Allocation

namespace Universality.Certificates

/-- Use the shorter side of binomial symmetry before the ratio recurrence. -/
def fastBinomial (top index : ℕ) : ℕ :=
  if index ≤ top then binomialByRatio top (min index (top - index)) else 0

theorem fastBinomial_eq_choose (top index : ℕ) : fastBinomial top index = top.choose index := by
  by_cases valid : index ≤ top
  · simp only [fastBinomial, if_pos valid, binomialByRatio_eq_choose]
    by_cases short : index ≤ top - index
    · rw [min_eq_left short]
    · rw [min_eq_right (by omega), Nat.choose_symm valid]
  · simp [fastBinomial, valid, Nat.choose_eq_zero_of_lt (by omega : top < index)]

/-- Length and zero count are carried, rather than rescanned at every suffix. -/
def fastFixedZeroLexRankAux : ℕ → ℕ → List Bool → ℕ
  | _, _, [] => 0
  | length, zeros, false :: rest => fastFixedZeroLexRankAux (length - 1) (zeros - 1) rest
  | length, zeros, true :: rest =>
      (if zeros = 0 then 0 else fastBinomial (length - 1) (zeros - 1)) +
        fastFixedZeroLexRankAux (length - 1) zeros rest

theorem fastFixedZeroLexRankAux_correct (word : List Bool) :
    fastFixedZeroLexRankAux word.length (zeroCount word) word = fixedZeroLexRank word := by
  induction word with
  | nil => rfl
  | cons bit word ih =>
      cases bit <;>
        simp [fastFixedZeroLexRankAux, fixedZeroLexRank, firstZeroWordCount,
          fastBinomial_eq_choose, binomialByRatio_eq_choose, ih]

def fastFixedZeroLexRank (word : List Bool) : ℕ :=
  fastFixedZeroLexRankAux word.length (zeroCount word) word

theorem fastFixedZeroLexRank_correct (word : List Bool) :
    fastFixedZeroLexRank word = fixedZeroLexRank word :=
  fastFixedZeroLexRankAux_correct word

def fastInitialAllocation (rows : List InitialAllocationRow) (word : List Bool) : ℕ :=
  let row := rows[zeroCount word]!
  (if word.headD false then row.firstTrue else row.firstFalse) +
    if fastFixedZeroLexRank word < row.remainder then 1 else 0

theorem fastInitialAllocation_correct (rows : List InitialAllocationRow) (word : List Bool) :
    fastInitialAllocation rows word = initialAllocation rows word := by
  simp only [fastInitialAllocation, initialAllocation, fastFixedZeroLexRank_correct]

def CorrectionPacket.fastCapacityCheck (rows : List InitialAllocationRow)
    (packet : CorrectionPacket) : Bool :=
  (binaryWords (2 * packet.layer + 1)).all (fun choices =>
    let value := (fastInitialAllocation rows (packet.word choices) : ℤ) +
      packet.coefficient * wordSign choices
    decide (0 ≤ value ∧ value ≤ 2 ^ packet.zeros))

theorem CorrectionPacket.fastCapacityCheck_iff (rows : List InitialAllocationRow)
    (packet : CorrectionPacket) :
    packet.fastCapacityCheck rows = true ↔ packet.capacityChecked rows := by
  simp [CorrectionPacket.fastCapacityCheck, CorrectionPacket.capacityChecked,
    fastInitialAllocation_correct, List.all_eq_true]

#print axioms CorrectionPacket.fastCapacityCheck_iff

end Universality.Certificates
