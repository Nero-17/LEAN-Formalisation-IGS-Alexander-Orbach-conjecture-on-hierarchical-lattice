import Universality.Certificates.Section5InitialMassBase19
import Universality.Certificates.Section5DataBase19
import Universality.Certificates.Section5MassSpecialization

namespace Universality.Certificates
open Matrix

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 10000 in
theorem allocationBase19_massRepairEvaluation :
    massEvaluationWithInitial 424 allocationBase19.packets allocationBase19InitialMass =
      massCertificateValue 424 19 := by
  decide +kernel

#print axioms allocationBase19_massRepairEvaluation

theorem allocationBase19_mass :
    Section5.allocationMassNumerator 424 allocationBase19.allocation *ᵥ
      (![55, 23] : Fin 2 → ℤ) =
      (16 ^ (424 + 1) * (19 : ℤ) ^ 219) • (![55, 23] : Fin 2 → ℤ) :=
  allocationBase19.mass_certificate_at 424 19 rfl allocationBase19_capacityValid
    allocationBase19InitialMass allocationBase19_initialMassEvaluation
    allocationBase19_massRepairEvaluation

#print axioms allocationBase19_mass
end Universality.Certificates
