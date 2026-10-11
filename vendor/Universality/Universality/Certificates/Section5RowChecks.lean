import Universality.Certificates.Section5LinearChecks

namespace Universality.Certificates

/-- Traverse rows and margins once, instead of repeatedly indexing the full
literal lists from every quantified zero count. -/
def uniformAllocationRowsCheck (depth zeros : ℕ) : List InitialAllocationRow → List ℕ → Bool
  | [], [] => true
  | row :: rows, slack :: slacks =>
      decide (row.hasUniformSlack depth zeros slack) &&
        uniformAllocationRowsCheck depth (zeros + 1) rows slacks
  | _, _ => false

theorem uniformAllocationRowsCheck_entry (depth start : ℕ)
    (rows : List InitialAllocationRow) (slacks : List ℕ)
    (checked : uniformAllocationRowsCheck depth start rows slacks = true)
    (index : ℕ) (bound : index < rows.length) :
    (rows[index]!).hasUniformSlack depth (start + index) (slacks[index]!) := by
  induction rows generalizing start slacks index with
  | nil => simp at bound
  | cons row rows induction_hypothesis =>
      cases slacks with
      | nil => simp [uniformAllocationRowsCheck] at checked
      | cons slack slacks =>
          simp only [uniformAllocationRowsCheck, Bool.and_eq_true, decide_eq_true_eq] at checked
          cases index with
          | zero => simpa using checked.1
          | succ index =>
              have entry := induction_hypothesis (start + 1) slacks checked.2 index
                (by simpa using bound)
              simpa only [List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm 1 index] using entry

theorem uniformAllocationRowsCheck_correct (certificate : CompressedAllocation)
    (length_checked : certificate.rows.length = certificate.depth + 1)
    (checked : uniformAllocationRowsCheck certificate.depth 0 certificate.rows certificate.slacks = true) :
    ∀ zeros ∈ List.range (certificate.depth + 1),
      (certificate.rows[zeros]!).hasUniformSlack certificate.depth zeros (certificate.slacks[zeros]!) := by
  intro zeros member
  have bound : zeros < certificate.rows.length := by
    rw [length_checked]
    exact List.mem_range.mp member
  simpa using uniformAllocationRowsCheck_entry certificate.depth 0 certificate.rows
    certificate.slacks checked zeros bound

end Universality.Certificates
