import Universality.Certificates.Section5MomentSpecialization
import Universality.Certificates.Section5GroupsBase19
import Universality.Certificates.Section5LengthCertificate

namespace Universality.Certificates

set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationBase19_volume :
    (5 : ℤ) ^ 424 + 4 * ((binaryWords 424).map fun word =>
      (allocationBase19.allocation word : ℤ) * 2 ^ zeroCount word).sum = 19 ^ 232 :=
  allocationBase19Moments.volume_identity_at allocationBase19 424 19 rfl rfl rfl
    allocationBase19_capacityValid
    certificateBase19_integer_moments allocationBase19_allCounts_valid
    allocationBase19_firstCounts_valid allocationBase19_groups_checked

theorem allocationBase19_thermal :
    8 * (13 : ℤ) ^ 424 + 5 * ((binaryWords 424).map fun word =>
      (allocationBase19.allocation word : ℤ) * 6 ^ zeroCount word).sum =
      8 ^ (424 + 1) * 19 ^ 70 :=
  allocationBase19Moments.thermal_identity_at allocationBase19 424 19 rfl rfl rfl
    allocationBase19_capacityValid
    certificateBase19_integer_moments allocationBase19_allCounts_valid
    allocationBase19_firstCounts_valid allocationBase19_groups_checked

theorem allocationBase19_volume_nat :
    5 ^ 424 + 4 * ((binaryWords 424).map fun word =>
      allocationBase19.allocation word * 2 ^ zeroCount word).sum = 19 ^ 232 :=
  allocationBase19Moments.volume_identity_nat_at allocationBase19 424 19 rfl rfl rfl
    allocationBase19_capacityValid
    certificateBase19_integer_moments allocationBase19_allCounts_valid
    allocationBase19_firstCounts_valid allocationBase19_groups_checked

theorem allocationBase19_thermal_nat :
    8 ^ (424 + 1) * 19 ^ 70 =
      8 * 13 ^ 424 + 5 * ((binaryWords 424).map fun word =>
        allocationBase19.allocation word * 6 ^ zeroCount word).sum :=
  allocationBase19Moments.thermal_identity_nat_at allocationBase19 424 19 rfl rfl rfl
    allocationBase19_capacityValid
    certificateBase19_integer_moments allocationBase19_allCounts_valid
    allocationBase19_firstCounts_valid allocationBase19_groups_checked

end Universality.Certificates
