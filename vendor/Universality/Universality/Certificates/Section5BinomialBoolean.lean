import Universality.Certificates.Section5BinomialTable

namespace Universality.Certificates

/-- A proof-free computation of the local binomial recurrences.  Correctness
is proved separately, so reduction need not traverse dependent transports. -/
def binomialTableCheck (top start expected : ℕ) : List ℕ → Bool
  | [] => true
  | value :: rest => (value == expected) &&
      binomialTableCheck top (start + 1) (value * (top - start) / (start + 1)) rest

theorem binomialTableCheck_iff (top start expected : ℕ) (values : List ℕ) :
    binomialTableCheck top start expected values = true ↔
      binomialTableChecked top start expected values := by
  induction values generalizing start expected with
  | nil => simp [binomialTableCheck, binomialTableChecked]
  | cons value rest induction_hypothesis =>
      simp only [binomialTableCheck, Bool.and_eq_true, beq_iff_eq,
        binomialTableChecked, induction_hypothesis]

theorem BinomialTable.valid_of_boolean (table : BinomialTable)
    (length_checked : table.values.length = table.top + 1)
    (entries_checked : binomialTableCheck table.top 0 1 table.values = true) :
    table.valid :=
  ⟨length_checked, (binomialTableCheck_iff table.top 0 1 table.values).mp entries_checked⟩

end Universality.Certificates
