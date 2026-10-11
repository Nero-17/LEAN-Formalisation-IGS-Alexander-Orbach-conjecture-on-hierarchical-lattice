import Universality.Certificates.Section5CapacityCertificate
import Mathlib.Data.List.Nodup

namespace Universality.Certificates

def correctionSignatureIndex (signature : ℕ × Bool × Bool) : ℕ :=
  4 * signature.1 + if signature.2.2 then
    (if signature.2.1 then 2 else 3) else (if signature.2.1 then 1 else 0)

def CorrectionPacket.index (packet : CorrectionPacket) : ℕ :=
  correctionSignatureIndex packet.signature

/-- Linear comparison with the list of consecutive packet indices replaces
the quadratic direct decision of pairwise disjointness. -/
theorem packets_pairwise_of_consecutive (packets : List CorrectionPacket)
    (checked : packets.map CorrectionPacket.index = List.range packets.length) :
    packets.Pairwise (fun packet other => packet.signature ≠ other.signature) := by
  have distinct : (packets.map CorrectionPacket.index).Nodup := by
    rw [checked]
    exact List.nodup_range
  change (packets.map CorrectionPacket.index).Pairwise (· ≠ ·) at distinct
  rw [List.pairwise_map] at distinct
  apply distinct.imp
  intro packet other different equal
  exact different (congrArg correctionSignatureIndex equal)

end Universality.Certificates
