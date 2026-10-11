import Universality.Certificates.Section5Sums
import Universality.Certificates.Section5InitialSums
import Universality.Certificates.Section5BinomialTable
import Universality.Certificates.IntegerMoments

namespace Universality.Certificates

theorem integerMoment_eq_range_sum (base : ℕ) (coefficients : List ℕ) :
    (integerMoment base coefficients : ℤ) =
      ((List.range coefficients.length).map fun index =>
        ((coefficients[index]! : ℕ) : ℤ) * (base : ℤ) ^ index).sum := by
  induction coefficients with
  | nil => simp [integerMoment]
  | cons coefficient rest induction_hypothesis =>
      simp only [integerMoment, Nat.cast_add, Nat.cast_mul, List.length_cons,
        List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map,
        Function.comp_def, List.getElem!_cons_zero, pow_zero, mul_one,
        List.getElem!_cons_succ, pow_succ]
      rw [induction_hypothesis]
      simp_rw [← mul_assoc]
      rw [List.sum_map_mul_right]
      ring

structure AllocationMomentCertificate where
  allocation : CompressedAllocation
  moments : IntegerMomentCertificate
  allCounts : BinomialTable
  firstCounts : BinomialTable

def AllocationMomentCertificate.groupChecked (certificate : AllocationMomentCertificate) : Prop :=
  certificate.allCounts.top = certificate.allocation.depth ∧
  certificate.firstCounts.top + 1 = certificate.allocation.depth ∧
  certificate.moments.depth = certificate.allocation.depth ∧
  (∀ zeros ∈ List.range (certificate.allocation.depth + 1),
    (certificate.allocation.rows[zeros]!).remainder ≤ certificate.allCounts.values[zeros]! ∧
    (if zeros = 0 then 0 else certificate.firstCounts.values[zeros - 1]!) *
        (certificate.allocation.rows[zeros]!).firstFalse +
      certificate.firstCounts.values[zeros]! * (certificate.allocation.rows[zeros]!).firstTrue +
      (certificate.allocation.rows[zeros]!).remainder = certificate.moments.zeroTotals[zeros]!)

instance (certificate : AllocationMomentCertificate) : Decidable certificate.groupChecked :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

theorem AllocationMomentCertificate.scalar_moment (certificate : AllocationMomentCertificate)
    (capacity_checked : certificate.allocation.capacityValid)
    (moments_checked : certificate.moments.valid)
    (allCounts_checked : certificate.allCounts.valid)
    (firstCounts_checked : certificate.firstCounts.valid)
    (groups_checked : certificate.groupChecked) (base : ℕ) :
    ((binaryWords certificate.allocation.depth).map fun word =>
      (certificate.allocation.allocation word : ℤ) * (base : ℤ) ^ zeroCount word).sum =
      integerMoment base certificate.moments.zeroTotals := by
  rw [certificate.allocation.corrected_scalar_moment capacity_checked]
  have depth_positive := capacity_checked.1
  have predecessor : certificate.allocation.depth - 1 + 1 = certificate.allocation.depth := by omega
  have range_depth : certificate.allocation.depth - 1 + 2 = certificate.allocation.depth + 1 := by omega
  have remainder_bound : ∀ zeros ∈ List.range (certificate.allocation.depth - 1 + 2),
      (certificate.allocation.rows[zeros]!).remainder ≤
        (certificate.allocation.depth - 1 + 1).choose zeros := by
    intro zeros member
    have checked := (groups_checked.2.2.2 zeros (by simpa only [range_depth] using member)).1
    rwa [certificate.allCounts.get_eq_choose allCounts_checked,
      groups_checked.1, ← predecessor] at checked
  have grouped := initialAllocation_grouped_moment certificate.allocation.rows
    (certificate.allocation.depth - 1) (fun zeros => (base : ℤ) ^ zeros) remainder_bound
  rw [predecessor, range_depth] at grouped
  rw [grouped, integerMoment_eq_range_sum]
  have totals_length : certificate.moments.zeroTotals.length = certificate.allocation.depth + 1 :=
    moments_checked.1.trans (congrArg (· + 1) groups_checked.2.2.1)
  rw [totals_length]
  congr 1
  apply List.map_congr_left
  intro zeros member
  congr 2
  have checked := (groups_checked.2.2.2 zeros member).2
  rw [certificate.firstCounts.get_eq_choose firstCounts_checked,
    certificate.firstCounts.get_eq_choose firstCounts_checked] at checked
  have first_depth : certificate.firstCounts.top = certificate.allocation.depth - 1 := by
    have := groups_checked.2.1
    omega
  rw [first_depth] at checked
  simpa only [firstZeroWordCount, binomialByRatio_eq_choose] using checked

theorem AllocationMomentCertificate.volume_identity (certificate : AllocationMomentCertificate)
    (capacity_checked : certificate.allocation.capacityValid)
    (moments_checked : certificate.moments.valid)
    (allCounts_checked : certificate.allCounts.valid)
    (firstCounts_checked : certificate.firstCounts.valid)
    (groups_checked : certificate.groupChecked) :
    (5 : ℤ) ^ certificate.allocation.depth + 4 *
      ((binaryWords certificate.allocation.depth).map fun word =>
        (certificate.allocation.allocation word : ℤ) * 2 ^ zeroCount word).sum =
      (certificate.moments.base : ℤ) ^ 232 := by
  have moment := certificate.scalar_moment capacity_checked moments_checked allCounts_checked
    firstCounts_checked groups_checked 2
  norm_num only [Nat.cast_ofNat] at moment
  rw [moment]
  have checked := moments_checked.2.2.1
  rw [groups_checked.2.2.1] at checked
  exact_mod_cast checked

theorem AllocationMomentCertificate.thermal_identity (certificate : AllocationMomentCertificate)
    (capacity_checked : certificate.allocation.capacityValid)
    (moments_checked : certificate.moments.valid)
    (allCounts_checked : certificate.allCounts.valid)
    (firstCounts_checked : certificate.firstCounts.valid)
    (groups_checked : certificate.groupChecked) :
    8 * (13 : ℤ) ^ certificate.allocation.depth + 5 *
      ((binaryWords certificate.allocation.depth).map fun word =>
        (certificate.allocation.allocation word : ℤ) * 6 ^ zeroCount word).sum =
      8 ^ (certificate.allocation.depth + 1) * (certificate.moments.base : ℤ) ^ 70 := by
  have moment := certificate.scalar_moment capacity_checked moments_checked allCounts_checked
    firstCounts_checked groups_checked 6
  norm_num only [Nat.cast_ofNat] at moment
  rw [moment]
  have checked := moments_checked.2.2.2
  rw [groups_checked.2.2.1] at checked
  exact_mod_cast checked

end Universality.Certificates
