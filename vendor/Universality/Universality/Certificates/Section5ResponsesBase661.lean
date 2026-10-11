import Universality.Certificates.Section5MomentSpecialization
import Universality.Certificates.Section5GroupsBase661
import Universality.Certificates.Section5LengthCertificate

namespace Universality.Certificates

set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase661_volume :
    (5 : ℤ) ^ 936 + 4 * ((binaryWords 936).map fun word =>
      (allocationBase661.allocation word : ℤ) * 2 ^ zeroCount word).sum = 661 ^ 232 :=
  allocationBase661Moments.volume_identity_at allocationBase661 936 661 rfl rfl rfl
    allocationBase661_capacityValid
    certificateBase661_integer_moments allocationBase661_allCounts_valid
    allocationBase661_firstCounts_valid allocationBase661_groups_checked

theorem allocationBase661_thermal :
    8 * (13 : ℤ) ^ 936 + 5 * ((binaryWords 936).map fun word =>
      (allocationBase661.allocation word : ℤ) * 6 ^ zeroCount word).sum =
      8 ^ (936 + 1) * 661 ^ 70 :=
  allocationBase661Moments.thermal_identity_at allocationBase661 936 661 rfl rfl rfl
    allocationBase661_capacityValid
    certificateBase661_integer_moments allocationBase661_allCounts_valid
    allocationBase661_firstCounts_valid allocationBase661_groups_checked

theorem allocationBase661_volume_nat :
    5 ^ 936 + 4 * ((binaryWords 936).map fun word =>
      allocationBase661.allocation word * 2 ^ zeroCount word).sum = 661 ^ 232 :=
  allocationBase661Moments.volume_identity_nat_at allocationBase661 936 661 rfl rfl rfl
    allocationBase661_capacityValid
    certificateBase661_integer_moments allocationBase661_allCounts_valid
    allocationBase661_firstCounts_valid allocationBase661_groups_checked

theorem allocationBase661_thermal_nat :
    8 ^ (936 + 1) * 661 ^ 70 =
      8 * 13 ^ 936 + 5 * ((binaryWords 936).map fun word =>
        allocationBase661.allocation word * 6 ^ zeroCount word).sum :=
  allocationBase661Moments.thermal_identity_nat_at allocationBase661 936 661 rfl rfl rfl
    allocationBase661_capacityValid
    certificateBase661_integer_moments allocationBase661_allCounts_valid
    allocationBase661_firstCounts_valid allocationBase661_groups_checked

end Universality.Certificates
