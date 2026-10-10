import Universality.Certificates.Section5CorrectedAllocation

namespace Universality.Certificates

structure CompressedAllocation where
  depth : ℕ
  rows : List InitialAllocationRow
  slacks : List ℕ
  packets : List CorrectionPacket
  deriving Inhabited

def CompressedAllocation.capacityValid (certificate : CompressedAllocation) : Prop :=
  0 < certificate.depth ∧
  certificate.rows.length = certificate.depth + 1 ∧
  certificate.slacks.length = certificate.depth + 1 ∧
  (∀ zeros ∈ List.range (certificate.depth + 1),
    (certificate.rows[zeros]!).hasSlack certificate.depth zeros (certificate.slacks[zeros]!)) ∧
  certificate.packets.Pairwise (fun packet other => packet.signature ≠ other.signature) ∧
  (∀ packet ∈ certificate.packets,
    2 * (2 * packet.layer + 1) + (packet.remaining + 2) = certificate.depth ∧
    (|packet.coefficient| ≤ (certificate.slacks[packet.zeros]! : ℤ) ∨
      packet.capacityChecked certificate.rows))

instance (certificate : CompressedAllocation) : Decidable certificate.capacityValid :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

theorem CompressedAllocation.initial_capacity (certificate : CompressedAllocation)
    (checked : certificate.capacityValid) (word : List Bool)
    (word_length : word.length = certificate.depth) :
    initialAllocation certificate.rows word ≤ 2 ^ zeroCount word := by
  have zero_bound : zeroCount word ∈ List.range (certificate.depth + 1) := by
    simp only [List.mem_range]
    have := zeroCount_le_length word
    omega
  have nonempty : word ≠ [] := by
    intro empty
    simp [empty] at word_length
    have positive := checked.1
    omega
  have bounds := initialAllocation_hasSlack certificate.rows word
    (certificate.slacks[zeroCount word]!) nonempty
    (by rw [word_length]; exact checked.2.2.2.1 _ zero_bound)
  omega

theorem CorrectionPacket.zeros_le_depth (packet : CorrectionPacket) (depth : ℕ)
    (length_checked : 2 * (2 * packet.layer + 1) + (packet.remaining + 2) = depth) :
    packet.zeros ≤ depth := by
  have tail_bound := zeroCount_le_length
    (correctionTail packet.first packet.repeated packet.remaining)
  rw [correctionTail_length] at tail_bound
  unfold CorrectionPacket.zeros
  omega

theorem CompressedAllocation.packet_capacities (certificate : CompressedAllocation)
    (checked : certificate.capacityValid) :
    ∀ packet ∈ certificate.packets, packet.capacityChecked certificate.rows := by
  intro packet member
  obtain ⟨length_checked, coefficient_or_checked⟩ := checked.2.2.2.2.2 packet member
  rcases coefficient_or_checked with coefficient_checked | exceptional_checked
  · exact packet.capacityChecked_of_slack certificate.rows certificate.depth
      (certificate.slacks[packet.zeros]!) length_checked
      (checked.2.2.2.1 packet.zeros (by
        simpa only [List.mem_range] using
          Nat.lt_succ_of_le (packet.zeros_le_depth certificate.depth length_checked)))
      coefficient_checked
  · exact exceptional_checked

def CompressedAllocation.allocation (certificate : CompressedAllocation) : List Bool → ℕ :=
  correctedAllocation certificate.rows certificate.packets

theorem CompressedAllocation.allocation_capacity (certificate : CompressedAllocation)
    (checked : certificate.capacityValid) (word : List Bool)
    (word_length : word.length = certificate.depth) :
    certificate.allocation word ≤ 2 ^ zeroCount word :=
  correctedAllocation_capacity certificate.rows certificate.packets word
    (certificate.initial_capacity checked word word_length) checked.2.2.2.2.1
    (certificate.packet_capacities checked)

theorem CompressedAllocation.allocation_coe (certificate : CompressedAllocation)
    (checked : certificate.capacityValid) (word : List Bool)
    (word_length : word.length = certificate.depth) :
    (certificate.allocation word : ℤ) =
      initialAllocation certificate.rows word +
        (certificate.packets.map fun packet => packet.adjustment word).sum := by
  exact correctedAllocation_coe certificate.rows certificate.packets word
    (correctedAllocationInt_bounds certificate.rows certificate.packets word
      (certificate.initial_capacity checked word word_length) checked.2.2.2.2.1
      (certificate.packet_capacities checked)).1

end Universality.Certificates
