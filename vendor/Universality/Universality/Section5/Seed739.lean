import Universality.Section5.CertificateConsequences
import Universality.Certificates.Section5MomentsBase739
import Universality.Certificates.Section5MassBase739

namespace Universality.Section5
noncomputable section
open Certificates

theorem exactAllocationBase739 :
    ExactAllocationCertificate 952 739 0 allocationBase739.allocation := by
  refine ⟨by decide, ?_, allocationBase739_length, allocationBase739_volume_nat,
    allocationBase739_thermal_nat, allocationBase739_mass⟩
  intro word member
  exact allocationBase739_capacity word (word_length_of_mem_binaryWords member)

def certifiedRule739 : Rule :=
  (allocatedExpression 952 (allocationDecoration allocationBase739.allocation)).rule

theorem certifiedRule739_responses : RuleResponses certifiedRule739 739 :=
  exactAllocationBase739.ruleResponses

end
end Universality.Section5
