import Universality.Certificates.Section5MassCertificate

/-! Exact additive decomposition of packet repair evaluation.
Each numerical chunk equality remains a required input until its kernel proof
is supplied. The flatten equality preserves the original packet order and
multiplicity; no packet or initial-stream obligation is omitted.
-/

namespace Universality.Certificates

theorem addIntegerMassPairs_assoc (first second third : ℤ × ℤ) :
    addIntegerMassPairs (addIntegerMassPairs first second) third =
      addIntegerMassPairs first (addIntegerMassPairs second third) := by
  cases first
  cases second
  cases third
  simp only [addIntegerMassPairs, add_assoc]

theorem addIntegerMassPairs_zero_left (value : ℤ × ℤ) :
    addIntegerMassPairs (0, 0) value = value := by
  cases value
  simp [addIntegerMassPairs]

theorem addIntegerMassPairs_zero_right (value : ℤ × ℤ) :
    addIntegerMassPairs value (0, 0) = value := by
  cases value
  simp [addIntegerMassPairs]

def sumIntegerMassPairs : List (ℤ × ℤ) → ℤ × ℤ
  | [] => (0, 0)
  | value :: values => addIntegerMassPairs value (sumIntegerMassPairs values)

theorem sumIntegerMassPairs_append (first second : List (ℤ × ℤ)) :
    sumIntegerMassPairs (first ++ second) =
      addIntegerMassPairs (sumIntegerMassPairs first) (sumIntegerMassPairs second) := by
  induction first with
  | nil => simp only [List.nil_append, sumIntegerMassPairs, addIntegerMassPairs_zero_left]
  | cons value values ih =>
      simp only [List.cons_append, sumIntegerMassPairs, ih, addIntegerMassPairs_assoc]

theorem correctionsMassEvaluation_append (first second : List CorrectionPacket) :
    correctionsMassEvaluation (first ++ second) =
      addIntegerMassPairs (correctionsMassEvaluation first) (correctionsMassEvaluation second) := by
  induction first with
  | nil => simp only [List.nil_append, correctionsMassEvaluation, addIntegerMassPairs_zero_left]
  | cons packet packets ih =>
      simp only [List.cons_append, correctionsMassEvaluation, ih, addIntegerMassPairs_assoc]

theorem correctionsMassEvaluation_take_drop (packets : List CorrectionPacket) (count : ℕ) :
    correctionsMassEvaluation packets =
      addIntegerMassPairs (correctionsMassEvaluation (packets.take count))
        (correctionsMassEvaluation (packets.drop count)) := by
  rw [← correctionsMassEvaluation_append, List.take_append_drop]

theorem correctionsMassEvaluation_flatten (chunks : List (List CorrectionPacket)) :
    correctionsMassEvaluation chunks.flatten =
      sumIntegerMassPairs (chunks.map correctionsMassEvaluation) := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
      simp only [List.flatten_cons, correctionsMassEvaluation_append, List.map_cons,
        sumIntegerMassPairs, ih]

theorem correctionsMassEvaluation_of_chunks
    (chunks : List (List CorrectionPacket)) (values : List (ℤ × ℤ))
    (checked : List.Forall₂
      (fun chunk value => correctionsMassEvaluation chunk = value) chunks values) :
    correctionsMassEvaluation chunks.flatten = sumIntegerMassPairs values := by
  induction checked with
  | nil => rfl
  | cons first rest ih =>
      simp only [List.flatten_cons, correctionsMassEvaluation_append,
        sumIntegerMassPairs, first, ih]

theorem massEvaluationWithInitial_of_chunks
    (depth : ℕ) (packets : List CorrectionPacket) (initialValue : ℕ × ℕ)
    (chunks : List (List CorrectionPacket)) (values : List (ℤ × ℤ))
    (baseline target : ℤ × ℤ)
    (parts : chunks.flatten = packets)
    (checked : List.Forall₂
      (fun chunk value => correctionsMassEvaluation chunk = value) chunks values)
    (baseline_checked : baselineMassEvaluation depth = baseline)
    (total_checked : addIntegerMassPairs
      (addIntegerMassPairs baseline ((initialValue.1 : ℤ), (initialValue.2 : ℤ)))
      (sumIntegerMassPairs values) = target) :
    massEvaluationWithInitial depth packets initialValue = target := by
  unfold massEvaluationWithInitial
  rw [← parts, correctionsMassEvaluation_of_chunks chunks values checked, baseline_checked]
  exact total_checked

end Universality.Certificates
