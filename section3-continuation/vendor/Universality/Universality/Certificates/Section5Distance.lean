import Universality.Certificates.Section5CapacityCertificate

namespace Universality.Certificates

theorem fixedZeroLexRank_replicate_false (count : ℕ) :
    fixedZeroLexRank (List.replicate count false) = 0 := by
  induction count with
  | zero => rfl
  | succ count induction_hypothesis =>
      simpa only [List.replicate_succ, fixedZeroLexRank] using induction_hypothesis

theorem CorrectionPacket.adjustment_all_zero (packet : CorrectionPacket) (count : ℕ) :
    packet.adjustment (List.replicate count false) = 0 := by
  by_contra nonzero
  obtain ⟨choices, choice_length, equal⟩ :=
    packet.support_of_adjustment_ne_zero _ nonzero
  have pair_count := congrArg initialOppositePairs equal
  simp only [CorrectionPacket.word, initialOppositePairs_paired_append,
    initialOppositePairs_replicate, choice_length] at pair_count
  omega

theorem CompressedAllocation.all_zero_value (certificate : CompressedAllocation)
    (checked : certificate.capacityValid) :
    certificate.allocation (List.replicate certificate.depth false) =
      (certificate.rows[certificate.depth]!).firstFalse +
        (if 0 < (certificate.rows[certificate.depth]!).remainder then 1 else 0) := by
  have int_value := certificate.allocation_coe checked
    (List.replicate certificate.depth false) (by simp)
  have zero_adjustments : (certificate.packets.map fun packet =>
      packet.adjustment (List.replicate certificate.depth false)).sum = 0 := by
    apply List.sum_eq_zero
    intro value member
    obtain ⟨packet, _, rfl⟩ := List.mem_map.mp member
    exact packet.adjustment_all_zero _
  rw [zero_adjustments, add_zero] at int_value
  have original := Int.natCast_inj.mp int_value
  rw [original]
  simp only [initialAllocation, fixedZeroLexRank_replicate_false,
    zeroCount, List.count_replicate_self]
  cases depth_equal : certificate.depth with
  | zero => simp only [depth_equal, List.replicate_zero, List.headD_nil, Bool.false_eq_true, ↓reduceIte]
  | succ depth => simp only [depth_equal, List.replicate_succ, List.headD_cons,
      Bool.false_eq_true, ↓reduceIte]

end Universality.Certificates
