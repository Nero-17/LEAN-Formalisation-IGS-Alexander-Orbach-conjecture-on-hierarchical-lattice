import Universality.Certificates.Section5NaturalMoments

/-! Project scalar fields before specializing large binary-word expressions.
The explicit equalities prevent endpoint conversion from needing to compare
an evaluated word list against a projected depth. -/

namespace Universality.Certificates

theorem AllocationMomentCertificate.volume_identity_nat_at
    (certificate : AllocationMomentCertificate) (allocation : CompressedAllocation)
    (depth base : ℕ)
    (allocation_eq : certificate.allocation = allocation)
    (depth_eq : allocation.depth = depth) (base_eq : certificate.moments.base = base)
    (capacity_checked : certificate.allocation.capacityValid)
    (moments_checked : certificate.moments.valid)
    (allCounts_checked : certificate.allCounts.valid)
    (firstCounts_checked : certificate.firstCounts.valid)
    (groups_checked : certificate.groupChecked) :
    5 ^ depth + 4 * ((binaryWords depth).map (fun word =>
      allocation.allocation word * 2 ^ zeroCount word)).sum = base ^ 232 := by
  have result := certificate.volume_identity_nat capacity_checked moments_checked
    allCounts_checked firstCounts_checked groups_checked
  rw [allocation_eq, depth_eq, base_eq] at result
  exact result

theorem AllocationMomentCertificate.thermal_identity_nat_at
    (certificate : AllocationMomentCertificate) (allocation : CompressedAllocation)
    (depth base : ℕ)
    (allocation_eq : certificate.allocation = allocation)
    (depth_eq : allocation.depth = depth) (base_eq : certificate.moments.base = base)
    (capacity_checked : certificate.allocation.capacityValid)
    (moments_checked : certificate.moments.valid)
    (allCounts_checked : certificate.allCounts.valid)
    (firstCounts_checked : certificate.firstCounts.valid)
    (groups_checked : certificate.groupChecked) :
    8 ^ (depth + 1) * base ^ 70 = 8 * 13 ^ depth +
      5 * ((binaryWords depth).map (fun word =>
        allocation.allocation word * 6 ^ zeroCount word)).sum := by
  have result := certificate.thermal_identity_nat capacity_checked moments_checked
    allCounts_checked firstCounts_checked groups_checked
  rw [allocation_eq, depth_eq, base_eq] at result
  exact result

theorem AllocationMomentCertificate.volume_identity_at
    (certificate : AllocationMomentCertificate) (allocation : CompressedAllocation)
    (depth base : ℕ)
    (allocation_eq : certificate.allocation = allocation)
    (depth_eq : allocation.depth = depth) (base_eq : certificate.moments.base = base)
    (capacity_checked : certificate.allocation.capacityValid)
    (moments_checked : certificate.moments.valid)
    (allCounts_checked : certificate.allCounts.valid)
    (firstCounts_checked : certificate.firstCounts.valid)
    (groups_checked : certificate.groupChecked) :
    (5 : ℤ) ^ depth + 4 * ((binaryWords depth).map (fun word =>
      (allocation.allocation word : ℤ) * 2 ^ zeroCount word)).sum = (base : ℤ) ^ 232 := by
  have result := certificate.volume_identity capacity_checked moments_checked
    allCounts_checked firstCounts_checked groups_checked
  rw [allocation_eq, depth_eq, base_eq] at result
  exact result

theorem AllocationMomentCertificate.thermal_identity_at
    (certificate : AllocationMomentCertificate) (allocation : CompressedAllocation)
    (depth base : ℕ)
    (allocation_eq : certificate.allocation = allocation)
    (depth_eq : allocation.depth = depth) (base_eq : certificate.moments.base = base)
    (capacity_checked : certificate.allocation.capacityValid)
    (moments_checked : certificate.moments.valid)
    (allCounts_checked : certificate.allCounts.valid)
    (firstCounts_checked : certificate.firstCounts.valid)
    (groups_checked : certificate.groupChecked) :
    8 * (13 : ℤ) ^ depth + 5 * ((binaryWords depth).map (fun word =>
      (allocation.allocation word : ℤ) * 6 ^ zeroCount word)).sum =
        8 ^ (depth + 1) * (base : ℤ) ^ 70 := by
  have result := certificate.thermal_identity capacity_checked moments_checked
    allCounts_checked firstCounts_checked groups_checked
  rw [allocation_eq, depth_eq, base_eq] at result
  exact result

end Universality.Certificates
