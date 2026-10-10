import Universality.Section5.ThreeSeedConsequences
import Universality.Section5.Seed19
import Universality.Section5.Seed739
import Universality.Section5.SeedShifted19
import Universality.Certificates.Section5MomentsBase661
import Universality.Certificates.Section5MassBase661

namespace Universality.Section5
noncomputable section
open Certificates

theorem exactAllocationBase661 :
    ExactAllocationCertificate 936 661 0 allocationBase661.allocation := by
  refine ⟨by decide, ?_, allocationBase661_length, allocationBase661_volume_nat,
    allocationBase661_thermal_nat, allocationBase661_mass⟩
  intro word member
  exact allocationBase661_capacity word (word_length_of_mem_binaryWords member)

def certifiedRule661 : Rule :=
  (allocatedExpression 936 (allocationDecoration allocationBase661.allocation)).rule

theorem certifiedRule661_responses : RuleResponses certifiedRule661 661 :=
  exactAllocationBase661.ruleResponses

theorem certified_three_scale_logs_independent :
    LinearIndependent ℚ
      ![Real.log (certifiedRule19.network.fullGraph.dist certifiedRule19.network.source
          certifiedRule19.network.target : ℝ),
        Real.log (certifiedRule661.network.fullGraph.dist certifiedRule661.network.source
          certifiedRule661.network.target : ℝ),
        Real.log (certifiedRule739.network.fullGraph.dist certifiedRule739.network.source
          certifiedRule739.network.target : ℝ)] :=
  ruleResponses_three_scale_logs_independent _ _ _ certifiedRule19_responses
    certifiedRule661_responses certifiedRule739_responses

def certifiedFamily : ℕ → Rule := compositionFamily certifiedRule19 certifiedRule661

theorem certifiedFamily_responses (index : ℕ) :
    RuleResponses (certifiedFamily index) (19 * 661 ^ index) :=
  compositionFamily_responses certifiedRule19_responses certifiedRule661_responses index

theorem certifiedFamily_injective : Function.Injective certifiedFamily :=
  compositionFamily_injective certifiedRule19_responses certifiedRule661_responses

theorem certifiedFamily_infinite : Set.Infinite (Set.range certifiedFamily) :=
  compositionFamily_infinite certifiedRule19_responses certifiedRule661_responses

theorem certifiedFamily_incommensurate {first second : ℕ} (different : first ≠ second) :
    ¬ ScaleCommensurate
      ((certifiedFamily first).network.fullGraph.dist
        (certifiedFamily first).network.source (certifiedFamily first).network.target)
      ((certifiedFamily second).network.fullGraph.dist
        (certifiedFamily second).network.source (certifiedFamily second).network.target) :=
  compositionFamily_incommensurate certifiedRule19_responses certifiedRule661_responses different


end
end Universality.Section5
