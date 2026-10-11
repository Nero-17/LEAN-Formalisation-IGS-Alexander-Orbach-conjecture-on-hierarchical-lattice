import Universality.Certificates.Section5MassRepairChecksBase739
import Universality.Certificates.Section5MassRepairProofBase73900
import Universality.Certificates.Section5MassRepairProofBase73901
import Universality.Certificates.Section5MassRepairProofBase73902
import Universality.Certificates.Section5MassRepairProofBase73903
import Universality.Certificates.Section5MassRepairProofBase73904
import Universality.Certificates.Section5MassRepairProofBase73905
import Universality.Certificates.Section5MassRepairProofBase73906
import Universality.Certificates.Section5MassRepairProofBase73907

namespace Universality.Certificates

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option exponentiation.threshold 10000
set_option Elab.async false

open MassRepairChunksBase739

theorem allocationBase739_repairChunksChecked :
    List.Forall₂ (fun chunk value => correctionsMassEvaluation chunk = value) chunks values :=
  (List.Forall₂.cons checked00 (List.Forall₂.cons checked01 (List.Forall₂.cons checked02 (List.Forall₂.cons checked03 (List.Forall₂.cons checked04 (List.Forall₂.cons checked05 (List.Forall₂.cons checked06 (List.Forall₂.cons checked07 (List.Forall₂.cons checked08 (List.Forall₂.cons checked09 (List.Forall₂.cons checked10 (List.Forall₂.cons checked11 (List.Forall₂.cons checked12 (List.Forall₂.cons checked13 (List.Forall₂.cons checked14 (List.Forall₂.cons checked15 (List.Forall₂.cons checked16 (List.Forall₂.cons checked17 (List.Forall₂.cons checked18 (List.Forall₂.cons checked19 (List.Forall₂.cons checked20 (List.Forall₂.cons checked21 (List.Forall₂.cons checked22 (List.Forall₂.cons checked23 (List.Forall₂.cons checked24 (List.Forall₂.cons checked25 (List.Forall₂.cons checked26 (List.Forall₂.cons checked27 (List.Forall₂.cons checked28 (List.Forall₂.cons checked29 List.Forall₂.nil))))))))))))))))))))))))))))))

theorem allocationBase739_massRepairLiteral :
    massEvaluationWithInitial 952 allocationBase739.packets allocationBase739RepairInitialMass =
      massCertificateValue 952 739 :=
  massEvaluationWithInitial_of_chunks 952 allocationBase739.packets allocationBase739RepairInitialMass
    chunks values baseline (massCertificateValue 952 739) parts_checked
    allocationBase739_repairChunksChecked baseline_checked total_checked

#print axioms allocationBase739_repairChunksChecked
#print axioms allocationBase739_massRepairLiteral
end Universality.Certificates
