import Universality.Section5.CertificateConsequences
import Universality.Certificates.Section5MomentsShifted19
import Universality.Certificates.Section5MassShifted19

namespace Universality.Section5
noncomputable section
open Certificates

theorem exactAllocationShifted19 :
    ExactAllocationCertificate 424 19 480 allocationShifted19.allocation := by
  refine ⟨by decide, ?_, allocationShifted19_length, allocationShifted19_volume_nat,
    allocationShifted19_thermal_nat, allocationShifted19_mass⟩
  intro word member
  exact allocationShifted19_capacity word (word_length_of_mem_binaryWords member)

def certifiedRuleShifted19 : Rule :=
  (allocatedExpression 424 (allocationDecoration allocationShifted19.allocation)).rule

theorem certifiedRuleShifted19_classical : certifiedRuleShifted19.Classical :=
  exactAllocationShifted19.classical

theorem certifiedRuleShifted19_transcendental_dimensions :
    Transcendental ℚ
      (Real.log (certifiedRuleShifted19.edges : ℝ) /
        Real.log (certifiedRuleShifted19.network.fullGraph.dist certifiedRuleShifted19.network.source
          certifiedRuleShifted19.network.target)) ∧
    Transcendental ℚ
      (Real.log ((_root_.spectralRadius ℂ
        ((certifiedRuleShifted19.network.massMatrix (1 / 2)).map Complex.ofReal)).toReal) /
        Real.log (certifiedRuleShifted19.network.fullGraph.dist certifiedRuleShifted19.network.source
          certifiedRuleShifted19.network.target)) ∧
    Transcendental ℚ
      (Real.log (deriv certifiedRuleShifted19.network.reliability (1 / 2)) /
        Real.log (certifiedRuleShifted19.network.fullGraph.dist certifiedRuleShifted19.network.source
          certifiedRuleShifted19.network.target)) :=
  exactAllocationShifted19.shifted_dimensions_transcendental

end
end Universality.Section5
