import Universality.Certificates.Section5MomentCertificate

namespace Universality.Certificates

theorem AllocationMomentCertificate.volume_identity_nat (certificate : AllocationMomentCertificate)
    (capacity_checked : certificate.allocation.capacityValid)
    (moments_checked : certificate.moments.valid)
    (allCounts_checked : certificate.allCounts.valid)
    (firstCounts_checked : certificate.firstCounts.valid)
    (groups_checked : certificate.groupChecked) :
    5 ^ certificate.allocation.depth + 4 *
      ((binaryWords certificate.allocation.depth).map fun word =>
        certificate.allocation.allocation word * 2 ^ zeroCount word).sum =
      certificate.moments.base ^ 232 := by
  apply Int.natCast_inj.mp
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_list_sum, List.map_map, Function.comp_def] using
    certificate.volume_identity capacity_checked moments_checked
      allCounts_checked firstCounts_checked groups_checked

theorem AllocationMomentCertificate.thermal_identity_nat (certificate : AllocationMomentCertificate)
    (capacity_checked : certificate.allocation.capacityValid)
    (moments_checked : certificate.moments.valid)
    (allCounts_checked : certificate.allCounts.valid)
    (firstCounts_checked : certificate.firstCounts.valid)
    (groups_checked : certificate.groupChecked) :
    8 ^ (certificate.allocation.depth + 1) * certificate.moments.base ^ 70 =
      8 * 13 ^ certificate.allocation.depth + 5 *
        ((binaryWords certificate.allocation.depth).map fun word =>
          certificate.allocation.allocation word * 6 ^ zeroCount word).sum := by
  apply Int.natCast_inj.mp
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_list_sum, List.map_map, Function.comp_def] using
    (certificate.thermal_identity capacity_checked moments_checked
      allCounts_checked firstCounts_checked groups_checked).symm

end Universality.Certificates
