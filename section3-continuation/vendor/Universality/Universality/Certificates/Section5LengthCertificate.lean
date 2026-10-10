import Universality.Certificates.Section5Distance

namespace Universality.Certificates

theorem CompressedAllocation.length_certificate (certificate : CompressedAllocation)
    (checked : certificate.capacityValid) (base offset : ℕ)
    (numerical_checked : 2 ^ certificate.depth +
      ((certificate.rows[certificate.depth]!).firstFalse +
        (if 0 < (certificate.rows[certificate.depth]!).remainder then 1 else 0)) =
      base ^ 100 + offset) :
    2 ^ certificate.depth + certificate.allocation (List.replicate certificate.depth false) =
      base ^ 100 + offset := by
  rw [certificate.all_zero_value checked]
  exact numerical_checked

end Universality.Certificates
