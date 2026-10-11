import Universality.Certificates.Section5Allocation

namespace Universality.Certificates

def unpairPrefix : ℕ → List Bool → Option (List Bool × List Bool)
  | 0, word => some ([], word)
  | count + 1, first :: second :: rest =>
      if first = second then none else
        (unpairPrefix count rest).map fun result => (first :: result.1, result.2)
  | _ + 1, _ => none

theorem unpairPrefix_paired (choices tail : List Bool) :
    unpairPrefix choices.length (pairedWord choices ++ tail) = some (choices, tail) := by
  induction choices with
  | nil => rfl
  | cons bit choices induction_hypothesis =>
      cases bit <;> simp [pairedWord, unpairPrefix, induction_hypothesis]

theorem unpairPrefix_spec {count : ℕ} {word choices tail : List Bool}
    (parsed : unpairPrefix count word = some (choices, tail)) :
    choices.length = count ∧ word = pairedWord choices ++ tail := by
  induction count generalizing word choices tail with
  | zero =>
      simp only [unpairPrefix, Option.some.injEq, Prod.mk.injEq] at parsed
      rcases parsed with ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | succ count induction_hypothesis =>
      cases word with
      | nil => simp [unpairPrefix] at parsed
      | cons first rest =>
          cases rest with
          | nil => simp [unpairPrefix] at parsed
          | cons second rest =>
              simp only [unpairPrefix] at parsed
              split at parsed
              · simp at parsed
              · rename_i different
                cases recursive : unpairPrefix count rest with
                | none => simp [recursive] at parsed
                | some result =>
                    rcases result with ⟨rest_choices, rest_tail⟩
                    simp only [recursive, Option.map_some, Option.some.injEq,
                      Prod.mk.injEq] at parsed
                    rcases parsed with ⟨rfl, rfl⟩
                    obtain ⟨length_checked, rfl⟩ := induction_hypothesis recursive
                    refine ⟨by simp [length_checked], ?_⟩
                    cases first <;> cases second <;> simp_all [pairedWord]

def CorrectionPacket.adjustment (packet : CorrectionPacket) (word : List Bool) : ℤ :=
  match unpairPrefix (2 * packet.layer + 1) word with
  | none => 0
  | some (choices, tail) =>
      if tail = correctionTail packet.first packet.repeated packet.remaining then
        packet.coefficient * wordSign choices else 0

theorem CorrectionPacket.adjustment_word (packet : CorrectionPacket) (choices : List Bool)
    (choice_length : choices.length = 2 * packet.layer + 1) :
    packet.adjustment (packet.word choices) = packet.coefficient * wordSign choices := by
  simp only [CorrectionPacket.adjustment, CorrectionPacket.word, ← choice_length,
    unpairPrefix_paired, ↓reduceIte]

theorem CorrectionPacket.support_of_adjustment_ne_zero (packet : CorrectionPacket)
    (word : List Bool) (nonzero : packet.adjustment word ≠ 0) :
    ∃ choices, choices.length = 2 * packet.layer + 1 ∧ packet.word choices = word := by
  unfold CorrectionPacket.adjustment at nonzero
  cases parsed : unpairPrefix (2 * packet.layer + 1) word with
  | none => simp [parsed] at nonzero
  | some result =>
      rcases result with ⟨choices, tail⟩
      simp only [parsed] at nonzero
      split at nonzero
      · rename_i equal
        obtain ⟨choice_length, word_equal⟩ := unpairPrefix_spec parsed
        exact ⟨choices, choice_length, by simpa [CorrectionPacket.word, equal] using word_equal.symm⟩
      · exact False.elim (nonzero rfl)

def CorrectionPacket.signature (packet : CorrectionPacket) : ℕ × Bool × Bool :=
  (packet.layer, packet.first, packet.repeated)

theorem CorrectionPacket.adjustments_disjoint (packet other : CorrectionPacket)
    (different : packet.signature ≠ other.signature) (word : List Bool)
    (nonzero : packet.adjustment word ≠ 0) : other.adjustment word = 0 := by
  by_contra other_nonzero
  obtain ⟨choices, choice_length, word_equal⟩ := packet.support_of_adjustment_ne_zero word nonzero
  obtain ⟨other_choices, other_length, other_equal⟩ :=
    other.support_of_adjustment_ne_zero word other_nonzero
  have unique := correction_support_unique choice_length other_length
    (word_equal.trans other_equal.symm)
  exact different (by simp only [CorrectionPacket.signature, unique.1, unique.2.2.1,
    unique.2.2.2.1])

theorem mem_binaryWords_of_length (word : List Bool) : word ∈ binaryWords word.length := by
  induction word with
  | nil => simp [binaryWords]
  | cons first rest induction_hypothesis =>
      cases first <;> simp [binaryWords, induction_hypothesis]

theorem CorrectionPacket.adjustment_capacity (packet : CorrectionPacket)
    (rows : List InitialAllocationRow) (word : List Bool)
    (base_bound : initialAllocation rows word ≤ 2 ^ zeroCount word)
    (checked : packet.capacityChecked rows) :
    0 ≤ (initialAllocation rows word : ℤ) + packet.adjustment word ∧
      (initialAllocation rows word : ℤ) + packet.adjustment word ≤ 2 ^ zeroCount word := by
  by_cases zero : packet.adjustment word = 0
  · simp only [zero, add_zero]
    exact ⟨Int.natCast_nonneg _, by exact_mod_cast base_bound⟩
  · obtain ⟨choices, choice_length, rfl⟩ := packet.support_of_adjustment_ne_zero word zero
    rw [packet.adjustment_word choices choice_length,
      packet.word_zeroCount choices choice_length]
    exact checked choices (choice_length ▸ mem_binaryWords_of_length choices)

def correctedAllocationInt (rows : List InitialAllocationRow)
    (packets : List CorrectionPacket) (word : List Bool) : ℤ :=
  initialAllocation rows word + (packets.map fun packet => packet.adjustment word).sum

def correctedAllocation (rows : List InitialAllocationRow)
    (packets : List CorrectionPacket) (word : List Bool) : ℕ :=
  (correctedAllocationInt rows packets word).toNat

theorem disjoint_adjustment_sum_bounds (initial capacity : ℤ)
    (packets : List CorrectionPacket) (word : List Bool)
    (base_bound : 0 ≤ initial ∧ initial ≤ capacity)
    (disjoint : packets.Pairwise fun packet other => packet.signature ≠ other.signature)
    (checked : ∀ packet ∈ packets,
      0 ≤ initial + packet.adjustment word ∧ initial + packet.adjustment word ≤ capacity) :
    0 ≤ initial + (packets.map fun packet => packet.adjustment word).sum ∧
      initial + (packets.map fun packet => packet.adjustment word).sum ≤ capacity := by
  induction packets with
  | nil => simpa using base_bound
  | cons packet packets induction_hypothesis =>
      rw [List.pairwise_cons] at disjoint
      by_cases zero : packet.adjustment word = 0
      · simpa only [List.map_cons, List.sum_cons, zero, zero_add] using
          induction_hypothesis disjoint.2 (fun other member => checked other (by simp [member]))
      · have rest_zero : (packets.map fun other => other.adjustment word).sum = 0 := by
          apply List.sum_eq_zero
          intro value member
          obtain ⟨other, other_member, rfl⟩ := List.mem_map.mp member
          exact packet.adjustments_disjoint other (disjoint.1 other other_member) word zero
        simpa only [List.map_cons, List.sum_cons, rest_zero, add_zero] using
          checked packet (by simp)

theorem correctedAllocationInt_bounds (rows : List InitialAllocationRow)
    (packets : List CorrectionPacket) (word : List Bool)
    (base_bound : initialAllocation rows word ≤ 2 ^ zeroCount word)
    (disjoint : packets.Pairwise fun packet other => packet.signature ≠ other.signature)
    (checked : ∀ packet ∈ packets, packet.capacityChecked rows) :
    0 ≤ correctedAllocationInt rows packets word ∧
      correctedAllocationInt rows packets word ≤ 2 ^ zeroCount word := by
  exact disjoint_adjustment_sum_bounds _ _ _ _
    ⟨Int.natCast_nonneg _, by exact_mod_cast base_bound⟩ disjoint
    (fun packet member => packet.adjustment_capacity rows word base_bound (checked packet member))

theorem correctedAllocation_coe (rows : List InitialAllocationRow)
    (packets : List CorrectionPacket) (word : List Bool)
    (nonnegative : 0 ≤ correctedAllocationInt rows packets word) :
    (correctedAllocation rows packets word : ℤ) = correctedAllocationInt rows packets word := by
  exact Int.toNat_of_nonneg nonnegative

theorem correctedAllocation_capacity (rows : List InitialAllocationRow)
    (packets : List CorrectionPacket) (word : List Bool)
    (base_bound : initialAllocation rows word ≤ 2 ^ zeroCount word)
    (disjoint : packets.Pairwise fun packet other => packet.signature ≠ other.signature)
    (checked : ∀ packet ∈ packets, packet.capacityChecked rows) :
    correctedAllocation rows packets word ≤ 2 ^ zeroCount word := by
  have bounds := correctedAllocationInt_bounds rows packets word base_bound disjoint checked
  have cast_bound : (correctedAllocation rows packets word : ℤ) ≤
      (2 ^ zeroCount word : ℕ) := by
    rw [correctedAllocation_coe rows packets word bounds.1]
    exact_mod_cast bounds.2
  exact_mod_cast cast_bound

end Universality.Certificates
