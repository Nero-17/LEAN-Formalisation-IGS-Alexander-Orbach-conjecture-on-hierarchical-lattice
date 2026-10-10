import Universality.Certificates.Section5MomentSpecialization
import Universality.Certificates.Section5GroupsShifted19
import Universality.Certificates.Section5LengthCertificate

namespace Universality.Certificates

set_option maxHeartbeats 200000
set_option maxRecDepth 100000
set_option exponentiation.threshold 4096

theorem allocationShifted19_volume :
    (5 : ℤ) ^ 424 + 4 * ((binaryWords 424).map fun word =>
      (allocationShifted19.allocation word : ℤ) * 2 ^ zeroCount word).sum = 19 ^ 232 :=
  allocationShifted19Moments.volume_identity_at allocationShifted19 424 19 rfl rfl rfl
    allocationShifted19_capacityValid
    certificateShifted19_integer_moments allocationShifted19_allCounts_valid
    allocationShifted19_firstCounts_valid allocationShifted19_groups_checked

theorem allocationShifted19_thermal :
    8 * (13 : ℤ) ^ 424 + 5 * ((binaryWords 424).map fun word =>
      (allocationShifted19.allocation word : ℤ) * 6 ^ zeroCount word).sum =
      8 ^ (424 + 1) * 19 ^ 70 :=
  allocationShifted19Moments.thermal_identity_at allocationShifted19 424 19 rfl rfl rfl
    allocationShifted19_capacityValid
    certificateShifted19_integer_moments allocationShifted19_allCounts_valid
    allocationShifted19_firstCounts_valid allocationShifted19_groups_checked

theorem allocationShifted19_volume_nat :
    5 ^ 424 + 4 * ((binaryWords 424).map fun word =>
      allocationShifted19.allocation word * 2 ^ zeroCount word).sum = 19 ^ 232 :=
  allocationShifted19Moments.volume_identity_nat_at allocationShifted19 424 19 rfl rfl rfl
    allocationShifted19_capacityValid
    certificateShifted19_integer_moments allocationShifted19_allCounts_valid
    allocationShifted19_firstCounts_valid allocationShifted19_groups_checked

theorem allocationShifted19_thermal_nat :
    8 ^ (424 + 1) * 19 ^ 70 =
      8 * 13 ^ 424 + 5 * ((binaryWords 424).map fun word =>
        allocationShifted19.allocation word * 6 ^ zeroCount word).sum :=
  allocationShifted19Moments.thermal_identity_nat_at allocationShifted19 424 19 rfl rfl rfl
    allocationShifted19_capacityValid
    certificateShifted19_integer_moments allocationShifted19_allCounts_valid
    allocationShifted19_firstCounts_valid allocationShifted19_groups_checked

end Universality.Certificates
