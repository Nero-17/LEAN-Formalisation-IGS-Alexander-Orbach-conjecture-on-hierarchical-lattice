import Universality.Certificates.Section5MassCertificate

namespace Universality.Certificates
open Matrix

/-- Rewrite the depth while symbolic, before a concrete endpoint can unfold
the binary-word sum hidden inside `allocationMassNumerator`. -/
theorem CompressedAllocation.mass_certificate_at (certificate : CompressedAllocation)
    (depth base : ℕ) (depth_eq : certificate.depth = depth)
    (checked : certificate.capacityValid) (initialValue : ℕ × ℕ)
    (initial_checked : initialMassEvaluation depth certificate.rows = initialValue)
    (numerical_checked : massEvaluationWithInitial depth certificate.packets initialValue =
      massCertificateValue depth base) :
    Section5.allocationMassNumerator depth certificate.allocation *ᵥ
      (![55, 23] : Fin 2 → ℤ) =
      (16 ^ (depth + 1) * (base : ℤ) ^ 219) • (![55, 23] : Fin 2 → ℤ) := by
  have initial_at_depth : initialMassEvaluation certificate.depth certificate.rows = initialValue := by
    rw [depth_eq]
    exact initial_checked
  have numerical_at_depth :
      massEvaluationWithInitial certificate.depth certificate.packets initialValue =
        massCertificateValue certificate.depth base := by
    rw [depth_eq]
    exact numerical_checked
  have result := certificate.mass_certificate checked base initialValue initial_at_depth numerical_at_depth
  rw [depth_eq] at result
  exact result

#print axioms CompressedAllocation.mass_certificate_at

end Universality.Certificates
