import Universality.Certificates.Section5CapacityCertificate
import Mathlib.Data.List.Nodup

namespace Universality.Certificates

theorem binaryWords_nodup (depth : ℕ) : (binaryWords depth).Nodup := by
  induction depth with
  | zero => simp [binaryWords]
  | succ depth induction_hypothesis =>
      rw [binaryWords, List.nodup_append]
      refine ⟨induction_hypothesis.map (by intro a b equal; exact List.cons.inj equal |>.2),
        induction_hypothesis.map (by intro a b equal; exact List.cons.inj equal |>.2), ?_⟩
      intro first first_member second second_member equal
      obtain ⟨first_word, _, first_equal⟩ := List.mem_map.mp first_member
      obtain ⟨second_word, _, second_equal⟩ := List.mem_map.mp second_member
      have impossible := first_equal.trans (equal.trans second_equal.symm)
      simp at impossible

theorem sum_single_indicator {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (words : List α) (nodup : words.Nodup) (word : α) (member : word ∈ words)
    (value : M) : (words.map fun other => if other = word then value else 0).sum = value := by
  rw [List.sum_map_eq_nsmul_single word]
  · rw [List.count_eq_one_of_mem nodup member]
    simp
  · intro other different _
    simp [different]

theorem sum_swap_lists {α β M : Type*} [AddCommMonoid M]
    (first : List α) (second : List β) (value : α → β → M) :
    (first.map fun a => (second.map (value a)).sum).sum =
      (second.map fun b => (first.map fun a => value a b).sum).sum := by
  induction first with
  | nil => simp
  | cons a first induction_hypothesis =>
      simp only [List.map_cons, List.sum_cons, induction_hypothesis, List.sum_map_add]

theorem CorrectionPacket.word_injective_on (packet : CorrectionPacket)
    {choices choices' : List Bool}
    (choice_length : choices.length = 2 * packet.layer + 1)
    (choice_length' : choices'.length = 2 * packet.layer + 1)
    (equal : packet.word choices = packet.word choices') : choices = choices' := by
  exact (correction_support_unique choice_length choice_length' equal).2.1

theorem CorrectionPacket.adjustment_eq_indicator_sum (packet : CorrectionPacket)
    (word : List Bool) :
    packet.adjustment word =
      ((binaryWords (2 * packet.layer + 1)).map fun choices =>
        if packet.word choices = word then packet.coefficient * wordSign choices else 0).sum := by
  by_cases supported : ∃ choices, choices.length = 2 * packet.layer + 1 ∧
      packet.word choices = word
  · obtain ⟨choices, choice_length, rfl⟩ := supported
    rw [packet.adjustment_word choices choice_length]
    symm
    have terms : ((binaryWords (2 * packet.layer + 1)).map fun other =>
          if packet.word other = packet.word choices then
            packet.coefficient * wordSign other else 0) =
        ((binaryWords (2 * packet.layer + 1)).map fun other =>
          if other = choices then packet.coefficient * wordSign choices else 0) := by
      apply List.map_congr_left
      intro other member
      by_cases equal : other = choices
      · simp [equal]
      · have unequal : packet.word other ≠ packet.word choices := by
          intro words_equal
          exact equal (packet.word_injective_on
            (word_length_of_mem_binaryWords member) choice_length words_equal)
        simp [equal, unequal]
    rw [terms]
    exact sum_single_indicator _ (binaryWords_nodup _) _
      (by simpa only [choice_length] using mem_binaryWords_of_length choices) _
  · have zero : packet.adjustment word = 0 := by
      by_contra nonzero
      exact supported (packet.support_of_adjustment_ne_zero word nonzero)
    rw [zero]
    symm
    apply List.sum_eq_zero
    intro value member
    obtain ⟨choices, choice_member, rfl⟩ := List.mem_map.mp member
    have unequal : packet.word choices ≠ word := by
      intro equal
      exact supported ⟨choices, word_length_of_mem_binaryWords choice_member, equal⟩
    simp [unequal]

theorem CorrectionPacket.weighted_sum (packet : CorrectionPacket) (depth : ℕ)
    (length_checked : 2 * (2 * packet.layer + 1) + (packet.remaining + 2) = depth)
    {M : Type*} [AddCommGroup M] (weight : List Bool → M) :
    ((binaryWords depth).map fun word => packet.adjustment word • weight word).sum =
      ((binaryWords (2 * packet.layer + 1)).map fun choices =>
        (packet.coefficient * wordSign choices) • weight (packet.word choices)).sum := by
  simp_rw [packet.adjustment_eq_indicator_sum]
  have distribute (choices : List (List Bool)) (word : List Bool) :
      (choices.map fun choice => if packet.word choice = word then
          packet.coefficient * wordSign choice else 0).sum • weight word =
      (choices.map fun choice => if packet.word choice = word then
          (packet.coefficient * wordSign choice) • weight word else 0).sum := by
    induction choices with
    | nil => simp
    | cons choice choices induction_hypothesis =>
        simp only [List.map_cons, List.sum_cons, add_smul, induction_hypothesis]
        congr 1
        split_ifs <;> simp
  simp_rw [distribute]
  rw [sum_swap_lists]
  congr 1
  apply List.map_congr_left
  intro choices member
  have choices_length := word_length_of_mem_binaryWords member
  have word_length : (packet.word choices).length = depth := by
    simpa only [CorrectionPacket.word, List.length_append, pairedWord_length,
      choices_length, correctionTail_length] using length_checked
  have word_member : packet.word choices ∈ binaryWords depth :=
    word_length ▸ mem_binaryWords_of_length (packet.word choices)
  have terms : ((binaryWords depth).map fun word =>
        if packet.word choices = word then
          (packet.coefficient * wordSign choices) • weight word else 0) =
      ((binaryWords depth).map fun word =>
        if word = packet.word choices then
          (packet.coefficient * wordSign choices) • weight (packet.word choices) else 0) := by
    apply List.map_congr_left
    intro word _
    by_cases equal : word = packet.word choices
    · simp [equal]
    · simp [equal, Ne.symm equal]
  rw [terms]
  exact sum_single_indicator _ (binaryWords_nodup _) _ word_member _

theorem CorrectionPacket.scalar_sum_zero (packet : CorrectionPacket) (depth : ℕ)
    (length_checked : 2 * (2 * packet.layer + 1) + (packet.remaining + 2) = depth)
    (weight : ℕ → ℤ) :
    ((binaryWords depth).map fun word =>
      packet.adjustment word * weight (zeroCount word)).sum = 0 := by
  have sum_reindex : ((binaryWords depth).map fun word =>
      packet.adjustment word * weight (zeroCount word)).sum =
      ((binaryWords (2 * packet.layer + 1)).map fun choices =>
        (packet.coefficient * wordSign choices) * weight (zeroCount (packet.word choices))).sum := by
    simpa [zsmul_eq_mul] using
      packet.weighted_sum depth length_checked (fun word => weight (zeroCount word))
  rw [sum_reindex]
  exact correction_scalar_sum packet.coefficient (2 * packet.layer)
    (correctionTail packet.first packet.repeated packet.remaining) weight

theorem correctedAllocationInt_weighted_sum (rows : List InitialAllocationRow)
    (packets : List CorrectionPacket) (depth : ℕ)
    {M : Type*} [AddCommGroup M] (weight : List Bool → M) :
    ((binaryWords depth).map fun word =>
      correctedAllocationInt rows packets word • weight word).sum =
      ((binaryWords depth).map fun word =>
        (initialAllocation rows word : ℤ) • weight word).sum +
      (packets.map fun packet => ((binaryWords depth).map fun word =>
        packet.adjustment word • weight word).sum).sum := by
  simp only [correctedAllocationInt, add_smul, List.sum_map_add]
  congr 1
  have distribute (packets : List CorrectionPacket) (word : List Bool) :
      (packets.map fun packet => packet.adjustment word).sum • weight word =
        (packets.map fun packet => packet.adjustment word • weight word).sum := by
    induction packets with
    | nil => simp
    | cons packet packets induction_hypothesis =>
        simp only [List.map_cons, List.sum_cons, add_smul, induction_hypothesis]
  simp_rw [distribute]
  exact sum_swap_lists _ _ _

theorem CompressedAllocation.corrected_scalar_moment (certificate : CompressedAllocation)
    (checked : certificate.capacityValid) (weight : ℕ → ℤ) :
    ((binaryWords certificate.depth).map fun word =>
      (certificate.allocation word : ℤ) * weight (zeroCount word)).sum =
      ((binaryWords certificate.depth).map fun word =>
        (initialAllocation certificate.rows word : ℤ) * weight (zeroCount word)).sum := by
  have casts : ((binaryWords certificate.depth).map fun word =>
        (certificate.allocation word : ℤ) * weight (zeroCount word)) =
      ((binaryWords certificate.depth).map fun word =>
        correctedAllocationInt certificate.rows certificate.packets word * weight (zeroCount word)) := by
    apply List.map_congr_left
    intro word member
    rw [certificate.allocation_coe checked word (word_length_of_mem_binaryWords member)]
    rfl
  rw [casts]
  have expanded := correctedAllocationInt_weighted_sum certificate.rows certificate.packets
    certificate.depth (fun word => weight (zeroCount word))
  simp [zsmul_eq_mul] at expanded
  rw [expanded]
  have corrections_zero : (certificate.packets.map fun packet =>
      ((binaryWords certificate.depth).map fun word =>
        packet.adjustment word * weight (zeroCount word)).sum).sum = 0 := by
    apply List.sum_eq_zero
    intro value member
    obtain ⟨packet, packet_member, rfl⟩ := List.mem_map.mp member
    exact packet.scalar_sum_zero certificate.depth
      (checked.2.2.2.2.2 packet packet_member).1 weight
  rw [corrections_zero, add_zero]

theorem CorrectionPacket.matrix_sum (packet : CorrectionPacket) (depth : ℕ)
    (length_checked : 2 * (2 * packet.layer + 1) + (packet.remaining + 2) = depth)
    (rightFactor : Matrix (Fin 2) (Fin 2) ℤ) :
    ((binaryWords depth).map fun word => packet.adjustment word •
      (wordProduct outerKernelNumerator centralKernelNumerator word * rightFactor)).sum =
      (packet.coefficient * 18 ^ packet.layer) •
        (!![-6, -6; 3, 6] * wordProduct outerKernelNumerator centralKernelNumerator
          (correctionTail packet.first packet.repeated packet.remaining) * rightFactor) := by
  rw [packet.weighted_sum depth length_checked]
  exact correction_mass_sum packet.coefficient packet.layer
    (correctionTail packet.first packet.repeated packet.remaining) rightFactor

theorem CompressedAllocation.corrected_matrix_sum (certificate : CompressedAllocation)
    (checked : certificate.capacityValid) (rightFactor : Matrix (Fin 2) (Fin 2) ℤ) :
    ((binaryWords certificate.depth).map fun word => (certificate.allocation word : ℤ) •
      (wordProduct outerKernelNumerator centralKernelNumerator word * rightFactor)).sum =
      ((binaryWords certificate.depth).map fun word =>
        (initialAllocation certificate.rows word : ℤ) •
          (wordProduct outerKernelNumerator centralKernelNumerator word * rightFactor)).sum +
      (certificate.packets.map fun packet => (packet.coefficient * 18 ^ packet.layer) •
        (!![-6, -6; 3, 6] * wordProduct outerKernelNumerator centralKernelNumerator
          (correctionTail packet.first packet.repeated packet.remaining) * rightFactor)).sum := by
  have casts : ((binaryWords certificate.depth).map fun word => (certificate.allocation word : ℤ) •
        (wordProduct outerKernelNumerator centralKernelNumerator word * rightFactor)) =
      ((binaryWords certificate.depth).map fun word =>
        correctedAllocationInt certificate.rows certificate.packets word •
          (wordProduct outerKernelNumerator centralKernelNumerator word * rightFactor)) := by
    apply List.map_congr_left
    intro word member
    rw [certificate.allocation_coe checked word (word_length_of_mem_binaryWords member)]
    rfl
  rw [casts, correctedAllocationInt_weighted_sum]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro packet member
  exact packet.matrix_sum certificate.depth (checked.2.2.2.2.2 packet member).1 rightFactor

end Universality.Certificates
