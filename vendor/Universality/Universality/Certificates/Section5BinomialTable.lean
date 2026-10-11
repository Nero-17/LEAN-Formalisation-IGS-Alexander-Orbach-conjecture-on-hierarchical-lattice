import Universality.Certificates.Section5Allocation

namespace Universality.Certificates

/-- Each transition is checked using its literal predecessor.  This avoids
recomputing a long binomial recurrence for every leaf-count group. -/
def binomialTableChecked (top start expected : ℕ) : List ℕ → Prop
  | [] => True
  | value :: rest => value = expected ∧
      binomialTableChecked top (start + 1) (value * (top - start) / (start + 1)) rest

instance (top start expected : ℕ) (values : List ℕ) :
    Decidable (binomialTableChecked top start expected values) := by
  induction values generalizing start expected with
  | nil => exact isTrue trivial
  | cons value rest induction_hypothesis =>
      unfold binomialTableChecked
      exact instDecidableAnd

theorem binomialTableChecked_entry (top start expected : ℕ) (values : List ℕ)
    (checked : binomialTableChecked top start expected values)
    (initial : expected = top.choose start) (index : ℕ) (bound : index < values.length) :
    values[index]! = top.choose (start + index) := by
  induction values generalizing start expected index with
  | nil => simp at bound
  | cons value rest induction_hypothesis =>
      rcases checked with ⟨value_checked, rest_checked⟩
      cases index with
      | zero => simpa using value_checked.trans initial
      | succ index =>
          have next : value * (top - start) / (start + 1) = top.choose (start + 1) := by
            rw [value_checked, initial, ← Nat.choose_succ_right_eq]
            exact Nat.mul_div_cancel _ (Nat.succ_pos _)
          have entry := induction_hypothesis (start + 1) _ rest_checked next index
            (by simpa using bound)
          simpa only [List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm 1 index] using entry

structure BinomialTable where
  top : ℕ
  values : List ℕ
  deriving Inhabited

def BinomialTable.valid (table : BinomialTable) : Prop :=
  table.values.length = table.top + 1 ∧ binomialTableChecked table.top 0 1 table.values

instance instDecidableBinomialTableValid (table : BinomialTable) : Decidable table.valid :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem BinomialTable.get_eq_choose (table : BinomialTable) (checked : table.valid)
    (index : ℕ) : table.values[index]! = table.top.choose index := by
  by_cases bound : index < table.values.length
  · simpa using binomialTableChecked_entry table.top 0 1 table.values checked.2
      (by simp) index bound
  · have above : table.top < index := by rw [checked.1] at bound; omega
    simp [getElem!_def, bound, Nat.choose_eq_zero_of_lt above]

end Universality.Certificates
