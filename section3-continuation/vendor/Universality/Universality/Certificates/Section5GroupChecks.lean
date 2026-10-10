import Universality.Certificates.Section5MomentCertificate

/-! A linear Boolean traversal for the scalar group identities. The first-count
list has one fewer entry in the intended certificate; headD 0 supplies its final
zero while the accumulator retains the preceding first-count value. -/

namespace Universality.Certificates

def linearGroupCheck (previousFirstCount : ℕ) :
    List InitialAllocationRow → List ℕ → List ℕ → List ℕ → Bool
  | [], [], _, [] => true
  | row :: rows, allCount :: allCounts, firstCounts, total :: totals =>
      decide (row.remainder ≤ allCount ∧
        previousFirstCount * row.firstFalse + firstCounts.headD 0 * row.firstTrue +
          row.remainder = total) &&
        linearGroupCheck (firstCounts.headD 0) rows allCounts firstCounts.tail totals
  | _, _, _, _ => false

private theorem natList_headD_get (values : List ℕ) : values.headD 0 = values[0]! := by
  cases values <;> rfl

private theorem natList_tail_get (values : List ℕ) (index : ℕ) :
    values.tail[index]! = values[index + 1]! := by
  cases values <;> simp

private theorem previousFirstCount_after_step (values : List ℕ) (index : ℕ) :
    (if index = 0 then values.headD 0 else values.tail[index - 1]!) = values[index]! := by
  cases values <;> cases index <;> simp

theorem linearGroupCheck_lengths (previousFirstCount : ℕ)
    (rows : List InitialAllocationRow) (allCounts firstCounts totals : List ℕ)
    (checked : linearGroupCheck previousFirstCount rows allCounts firstCounts totals = true) :
    rows.length = allCounts.length ∧ rows.length = totals.length := by
  induction rows generalizing previousFirstCount allCounts firstCounts totals with
  | nil =>
      cases allCounts <;> cases totals <;> simp_all [linearGroupCheck]
  | cons row rows induction_hypothesis =>
      cases allCounts with
      | nil => simp [linearGroupCheck] at checked
      | cons allCount allCounts =>
          cases totals with
          | nil => simp [linearGroupCheck] at checked
          | cons total totals =>
              simp only [linearGroupCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
              obtain ⟨all_length, totals_length⟩ := induction_hypothesis
                (firstCounts.headD 0) allCounts firstCounts.tail totals checked.2
              exact ⟨congrArg Nat.succ all_length, congrArg Nat.succ totals_length⟩

theorem linearGroupCheck_correct (previousFirstCount : ℕ)
    (rows : List InitialAllocationRow) (allCounts firstCounts totals : List ℕ)
    (checked : linearGroupCheck previousFirstCount rows allCounts firstCounts totals = true)
    (index : ℕ) (valid : index < rows.length) :
    (rows[index]!).remainder ≤ allCounts[index]! ∧
      (if index = 0 then previousFirstCount else firstCounts[index - 1]!) *
          (rows[index]!).firstFalse +
        firstCounts[index]! * (rows[index]!).firstTrue + (rows[index]!).remainder = totals[index]! := by
  induction rows generalizing previousFirstCount allCounts firstCounts totals index with
  | nil => simp at valid
  | cons row rows induction_hypothesis =>
      cases allCounts with
      | nil => simp [linearGroupCheck] at checked
      | cons allCount allCounts =>
          cases totals with
          | nil => simp [linearGroupCheck] at checked
          | cons total totals =>
              simp only [linearGroupCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
              obtain ⟨head_checked, tail_checked⟩ := checked
              cases index with
              | zero =>
                  rw [natList_headD_get] at head_checked
                  simpa using head_checked
              | succ index =>
                  have tail_result := induction_hypothesis (firstCounts.headD 0) allCounts
                    firstCounts.tail totals tail_checked index (by simpa using valid)
                  rw [previousFirstCount_after_step, natList_tail_get] at tail_result
                  simpa using tail_result

theorem AllocationMomentCertificate.groupChecked_of_linear
    (certificate : AllocationMomentCertificate)
    (all_top : certificate.allCounts.top = certificate.allocation.depth)
    (first_top : certificate.firstCounts.top + 1 = certificate.allocation.depth)
    (moment_depth : certificate.moments.depth = certificate.allocation.depth)
    (rows_length : certificate.allocation.rows.length = certificate.allocation.depth + 1)
    (checked : linearGroupCheck 0 certificate.allocation.rows certificate.allCounts.values
      certificate.firstCounts.values certificate.moments.zeroTotals = true) :
    certificate.groupChecked := by
  refine ⟨all_top, first_top, moment_depth, ?_⟩
  intro zeros member
  exact linearGroupCheck_correct 0 certificate.allocation.rows certificate.allCounts.values
    certificate.firstCounts.values certificate.moments.zeroTotals checked zeros
    (by simpa only [List.mem_range, ← rows_length] using member)

#print axioms linearGroupCheck_correct
#print axioms AllocationMomentCertificate.groupChecked_of_linear

end Universality.Certificates
