import Universality.Certificates.Section5InitialMassBase739
import Universality.Certificates.Section5DataBase739
import Universality.Certificates.Section5MassSpecialization
import Universality.Certificates.Section5MassRepairBase739

namespace Universality.Certificates
open Matrix

theorem allocationBase739_massRepairEvaluation :
    massEvaluationWithInitial 952 allocationBase739.packets allocationBase739InitialMass =
      massCertificateValue 952 739 := by
  simpa only [allocationBase739InitialMass, allocationBase739RepairInitialMass] using
    allocationBase739_massRepairLiteral

#print axioms allocationBase739_massRepairEvaluation

theorem allocationBase739_mass :
    Section5.allocationMassNumerator 952 allocationBase739.allocation *ᵥ
      (![55, 23] : Fin 2 → ℤ) =
      (16 ^ (952 + 1) * (739 : ℤ) ^ 219) • (![55, 23] : Fin 2 → ℤ) :=
  allocationBase739.mass_certificate_at 952 739 rfl allocationBase739_capacityValid
    allocationBase739InitialMass allocationBase739_initialMassEvaluation
    allocationBase739_massRepairEvaluation

#print axioms allocationBase739_mass
end Universality.Certificates
