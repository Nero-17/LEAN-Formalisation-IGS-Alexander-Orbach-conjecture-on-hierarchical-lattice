import Universality.Certificates.Section5CapacityCertificate

namespace Universality.Certificates

def CorrectionPacket.fastZeros (packet : CorrectionPacket) : ℕ :=
  (2 * packet.layer + 1) + (if packet.first then 0 else 1) +
    (if packet.repeated then 0 else packet.remaining + 1)

theorem CorrectionPacket.fastZeros_correct (packet : CorrectionPacket) :
    packet.fastZeros = packet.zeros := by
  cases first : packet.first <;> cases repeated : packet.repeated <;>
    simp [CorrectionPacket.fastZeros, CorrectionPacket.zeros, correctionTail, zeroCount,
      first, repeated, List.count_replicate, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] <;> omega

/-- A Boolean packet traversal with a separately verified exceptional checker.
The short-circuit alternative retains the slack coverage of ordinary packets. -/
def allocationPacketCheck (depth : ℕ) (slacks : List ℕ)
    (exceptionCheck : CorrectionPacket → Bool) (packet : CorrectionPacket) : Bool :=
  decide (2 * (2 * packet.layer + 1) + (packet.remaining + 2) = depth) &&
    (decide (|packet.coefficient| ≤ (slacks[packet.zeros]! : ℤ)) || exceptionCheck packet)

def allocationPacketsCheck (depth : ℕ) (slacks : List ℕ)
    (exceptionCheck : CorrectionPacket → Bool) (packets : List CorrectionPacket) : Bool :=
  packets.all (allocationPacketCheck depth slacks exceptionCheck)

theorem allocationPacketsCheck_correct (depth : ℕ) (slacks : List ℕ)
    (rows : List InitialAllocationRow) (exceptionCheck : CorrectionPacket → Bool)
    (packets : List CorrectionPacket)
    (exception_correct : ∀ packet ∈ packets,
      exceptionCheck packet = true → packet.capacityChecked rows)
    (checked : allocationPacketsCheck depth slacks exceptionCheck packets = true) :
    ∀ packet ∈ packets,
      2 * (2 * packet.layer + 1) + (packet.remaining + 2) = depth ∧
        (|packet.coefficient| ≤ (slacks[packet.zeros]! : ℤ) ∨ packet.capacityChecked rows) := by
  intro packet member
  have entry := List.all_eq_true.mp checked packet member
  simp only [allocationPacketCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at entry
  refine ⟨entry.1, ?_⟩
  exact entry.2.imp id (exception_correct packet member)

def ordinaryPacketExceptionCheck (rows : List InitialAllocationRow)
    (packet : CorrectionPacket) : Bool := decide (packet.capacityChecked rows)

theorem ordinaryPacketExceptionCheck_correct (rows : List InitialAllocationRow)
    (packet : CorrectionPacket) (checked : ordinaryPacketExceptionCheck rows packet = true) :
    packet.capacityChecked rows := of_decide_eq_true checked

theorem allocationPacketsCheck_ordinary_correct (depth : ℕ) (slacks : List ℕ)
    (rows : List InitialAllocationRow) (packets : List CorrectionPacket)
    (checked : allocationPacketsCheck depth slacks (ordinaryPacketExceptionCheck rows) packets = true) :
    ∀ packet ∈ packets,
      2 * (2 * packet.layer + 1) + (packet.remaining + 2) = depth ∧
        (|packet.coefficient| ≤ (slacks[packet.zeros]! : ℤ) ∨ packet.capacityChecked rows) :=
  allocationPacketsCheck_correct depth slacks rows (ordinaryPacketExceptionCheck rows) packets
    (fun packet _ => ordinaryPacketExceptionCheck_correct rows packet) checked

def allocationPacketCheckFast (depth : ℕ) (slacks : List ℕ)
    (exceptionCheck : CorrectionPacket → Bool) (packet : CorrectionPacket) : Bool :=
  decide (2 * (2 * packet.layer + 1) + (packet.remaining + 2) = depth) &&
    (decide (|packet.coefficient| ≤ (slacks[packet.fastZeros]! : ℤ)) || exceptionCheck packet)

def allocationPacketsCheckFast (depth : ℕ) (slacks : List ℕ)
    (exceptionCheck : CorrectionPacket → Bool) (packets : List CorrectionPacket) : Bool :=
  packets.all (allocationPacketCheckFast depth slacks exceptionCheck)

theorem allocationPacketsCheckFast_correct (depth : ℕ) (slacks : List ℕ)
    (rows : List InitialAllocationRow) (exceptionCheck : CorrectionPacket → Bool)
    (packets : List CorrectionPacket)
    (exception_correct : ∀ packet ∈ packets,
      exceptionCheck packet = true → packet.capacityChecked rows)
    (checked : allocationPacketsCheckFast depth slacks exceptionCheck packets = true) :
    ∀ packet ∈ packets,
      2 * (2 * packet.layer + 1) + (packet.remaining + 2) = depth ∧
        (|packet.coefficient| ≤ (slacks[packet.zeros]! : ℤ) ∨ packet.capacityChecked rows) := by
  intro packet member
  have entry := List.all_eq_true.mp checked packet member
  simp only [allocationPacketCheckFast, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    CorrectionPacket.fastZeros_correct] at entry
  exact ⟨entry.1, entry.2.imp id (exception_correct packet member)⟩

end Universality.Certificates
