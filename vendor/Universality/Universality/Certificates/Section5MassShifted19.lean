import Universality.Certificates.Section5InitialMassShifted19
import Universality.Certificates.Section5DataShifted19
import Universality.Certificates.Section5MassSpecialization

namespace Universality.Certificates
open Matrix

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 10000 in
theorem allocationShifted19_massRepairEvaluation :
    massEvaluationWithInitial 424 allocationShifted19.packets allocationShifted19InitialMass =
      massCertificateValue 424 19 := by
  decide +kernel

#print axioms allocationShifted19_massRepairEvaluation

theorem allocationShifted19_mass :
    Section5.allocationMassNumerator 424 allocationShifted19.allocation *ᵥ
      (![55, 23] : Fin 2 → ℤ) =
      (16 ^ (424 + 1) * (19 : ℤ) ^ 219) • (![55, 23] : Fin 2 → ℤ) :=
  allocationShifted19.mass_certificate_at 424 19 rfl allocationShifted19_capacityValid
    allocationShifted19InitialMass allocationShifted19_initialMassEvaluation
    allocationShifted19_massRepairEvaluation

#print axioms allocationShifted19_mass
end Universality.Certificates
