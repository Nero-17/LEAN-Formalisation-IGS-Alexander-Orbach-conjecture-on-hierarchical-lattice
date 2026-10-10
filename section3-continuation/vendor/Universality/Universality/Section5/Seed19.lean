import Universality.Section5.CertificateConsequences
import Universality.Certificates.Section5MomentsBase19
import Universality.Certificates.Section5MassBase19

namespace Universality.Section5
noncomputable section
open Certificates

theorem exactAllocationBase19 :
    ExactAllocationCertificate 424 19 0 allocationBase19.allocation := by
  refine ⟨by decide, ?_, allocationBase19_length, allocationBase19_volume_nat,
    allocationBase19_thermal_nat, allocationBase19_mass⟩
  intro word member
  exact allocationBase19_capacity word (word_length_of_mem_binaryWords member)

def certifiedRule19 : Rule :=
  (allocatedExpression 424 (allocationDecoration allocationBase19.allocation)).rule

theorem certifiedRule19_responses : RuleResponses certifiedRule19 19 :=
  exactAllocationBase19.ruleResponses

end
end Universality.Section5
