import Universality.Certificates.Section5InitialMassBase661
import Universality.Certificates.Section5DataBase661
import Universality.Certificates.Section5MassSpecialization
import Universality.Certificates.Section5MassRepairBase661

namespace Universality.Certificates
open Matrix

theorem allocationBase661_massRepairEvaluation :
    massEvaluationWithInitial 936 allocationBase661.packets allocationBase661InitialMass =
      massCertificateValue 936 661 := by
  simpa only [allocationBase661InitialMass, allocationBase661RepairInitialMass] using
    allocationBase661_massRepairLiteral

#print axioms allocationBase661_massRepairEvaluation

theorem allocationBase661_mass :
    Section5.allocationMassNumerator 936 allocationBase661.allocation *ᵥ
      (![55, 23] : Fin 2 → ℤ) =
      (16 ^ (936 + 1) * (661 : ℤ) ^ 219) • (![55, 23] : Fin 2 → ℤ) :=
  allocationBase661.mass_certificate_at 936 661 rfl allocationBase661_capacityValid
    allocationBase661InitialMass allocationBase661_initialMassEvaluation
    allocationBase661_massRepairEvaluation

#print axioms allocationBase661_mass
end Universality.Certificates
