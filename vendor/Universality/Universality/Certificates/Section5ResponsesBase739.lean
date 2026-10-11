import Universality.Certificates.Section5MomentSpecialization
import Universality.Certificates.Section5GroupsBase739
import Universality.Certificates.Section5LengthCertificate

namespace Universality.Certificates

set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase739_volume :
    (5 : ℤ) ^ 952 + 4 * ((binaryWords 952).map fun word =>
      (allocationBase739.allocation word : ℤ) * 2 ^ zeroCount word).sum = 739 ^ 232 :=
  allocationBase739Moments.volume_identity_at allocationBase739 952 739 rfl rfl rfl
    allocationBase739_capacityValid
    certificateBase739_integer_moments allocationBase739_allCounts_valid
    allocationBase739_firstCounts_valid allocationBase739_groups_checked

theorem allocationBase739_thermal :
    8 * (13 : ℤ) ^ 952 + 5 * ((binaryWords 952).map fun word =>
      (allocationBase739.allocation word : ℤ) * 6 ^ zeroCount word).sum =
      8 ^ (952 + 1) * 739 ^ 70 :=
  allocationBase739Moments.thermal_identity_at allocationBase739 952 739 rfl rfl rfl
    allocationBase739_capacityValid
    certificateBase739_integer_moments allocationBase739_allCounts_valid
    allocationBase739_firstCounts_valid allocationBase739_groups_checked

theorem allocationBase739_volume_nat :
    5 ^ 952 + 4 * ((binaryWords 952).map fun word =>
      allocationBase739.allocation word * 2 ^ zeroCount word).sum = 739 ^ 232 :=
  allocationBase739Moments.volume_identity_nat_at allocationBase739 952 739 rfl rfl rfl
    allocationBase739_capacityValid
    certificateBase739_integer_moments allocationBase739_allCounts_valid
    allocationBase739_firstCounts_valid allocationBase739_groups_checked

theorem allocationBase739_thermal_nat :
    8 ^ (952 + 1) * 739 ^ 70 =
      8 * 13 ^ 952 + 5 * ((binaryWords 952).map fun word =>
        allocationBase739.allocation word * 6 ^ zeroCount word).sum :=
  allocationBase739Moments.thermal_identity_nat_at allocationBase739 952 739 rfl rfl rfl
    allocationBase739_capacityValid
    certificateBase739_integer_moments allocationBase739_allCounts_valid
    allocationBase739_firstCounts_valid allocationBase739_groups_checked

end Universality.Certificates
