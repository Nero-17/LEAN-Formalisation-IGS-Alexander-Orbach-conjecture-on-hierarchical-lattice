import Universality.Certificates.Section5MassRepairChecksBase661
import Universality.Certificates.Section5MassRepairProofBase66100
import Universality.Certificates.Section5MassRepairProofBase66101
import Universality.Certificates.Section5MassRepairProofBase66102
import Universality.Certificates.Section5MassRepairProofBase66103
import Universality.Certificates.Section5MassRepairProofBase66104
import Universality.Certificates.Section5MassRepairProofBase66105
import Universality.Certificates.Section5MassRepairProofBase66106
import Universality.Certificates.Section5MassRepairProofBase66107

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

open MassRepairChunksBase661

theorem allocationBase661_repairChunksChecked :
    List.Forall₂ (fun chunk value => correctionsMassEvaluation chunk = value) chunks values :=
  (List.Forall₂.cons checked00 (List.Forall₂.cons checked01 (List.Forall₂.cons checked02 (List.Forall₂.cons checked03 (List.Forall₂.cons checked04 (List.Forall₂.cons checked05 (List.Forall₂.cons checked06 (List.Forall₂.cons checked07 (List.Forall₂.cons checked08 (List.Forall₂.cons checked09 (List.Forall₂.cons checked10 (List.Forall₂.cons checked11 (List.Forall₂.cons checked12 (List.Forall₂.cons checked13 (List.Forall₂.cons checked14 (List.Forall₂.cons checked15 (List.Forall₂.cons checked16 (List.Forall₂.cons checked17 (List.Forall₂.cons checked18 (List.Forall₂.cons checked19 (List.Forall₂.cons checked20 (List.Forall₂.cons checked21 (List.Forall₂.cons checked22 (List.Forall₂.cons checked23 (List.Forall₂.cons checked24 (List.Forall₂.cons checked25 (List.Forall₂.cons checked26 (List.Forall₂.cons checked27 (List.Forall₂.cons checked28 (List.Forall₂.cons checked29 List.Forall₂.nil))))))))))))))))))))))))))))))

theorem allocationBase661_massRepairLiteral :
    massEvaluationWithInitial 936 allocationBase661.packets allocationBase661RepairInitialMass =
      massCertificateValue 936 661 :=
  massEvaluationWithInitial_of_chunks 936 allocationBase661.packets allocationBase661RepairInitialMass
    chunks values baseline (massCertificateValue 936 661) parts_checked
    allocationBase661_repairChunksChecked baseline_checked total_checked

#print axioms allocationBase661_repairChunksChecked
#print axioms allocationBase661_massRepairLiteral
end Universality.Certificates
