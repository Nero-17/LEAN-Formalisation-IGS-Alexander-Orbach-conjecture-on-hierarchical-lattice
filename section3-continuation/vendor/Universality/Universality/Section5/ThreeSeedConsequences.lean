import Universality.Section5.CertificateConsequences
import Universality.Section5.ScaleIndependence

namespace Universality.Section5
noncomputable section

theorem ruleResponses_three_scale_logs_independent (first second third : Rule)
    (firstResponse : RuleResponses first 19)
    (secondResponse : RuleResponses second 661)
    (thirdResponse : RuleResponses third 739) :
    LinearIndependent ℚ
      ![Real.log (first.network.fullGraph.dist first.network.source first.network.target : ℝ),
        Real.log (second.network.fullGraph.dist second.network.source second.network.target : ℝ),
        Real.log (third.network.fullGraph.dist third.network.source third.network.target : ℝ)] := by
  rw [firstResponse.distance, secondResponse.distance, thirdResponse.distance]
  simpa only [Nat.cast_pow, Nat.cast_ofNat] using three_actual_scale_logs_independent

/-- The three exact allocation certificates produce actual classical rules
with the stated responses and independent scale logarithms. -/
theorem exactCertificates_three_rules
    {firstDepth secondDepth thirdDepth : ℕ}
    {firstAllocation secondAllocation thirdAllocation : List Bool → ℕ}
    (firstCertificate : ExactAllocationCertificate firstDepth 19 0 firstAllocation)
    (secondCertificate : ExactAllocationCertificate secondDepth 661 0 secondAllocation)
    (thirdCertificate : ExactAllocationCertificate thirdDepth 739 0 thirdAllocation) :
    ∃ first second third : Rule,
      RuleResponses first 19 ∧ RuleResponses second 661 ∧ RuleResponses third 739 ∧
      LinearIndependent ℚ
        ![Real.log (first.network.fullGraph.dist first.network.source first.network.target : ℝ),
          Real.log (second.network.fullGraph.dist second.network.source second.network.target : ℝ),
          Real.log (third.network.fullGraph.dist third.network.source third.network.target : ℝ)] := by
  refine ⟨(allocatedExpression firstDepth (allocationDecoration firstAllocation)).rule,
    (allocatedExpression secondDepth (allocationDecoration secondAllocation)).rule,
    (allocatedExpression thirdDepth (allocationDecoration thirdAllocation)).rule,
    firstCertificate.ruleResponses, secondCertificate.ruleResponses, thirdCertificate.ruleResponses, ?_⟩
  exact ruleResponses_three_scale_logs_independent _ _ _ firstCertificate.ruleResponses
    secondCertificate.ruleResponses thirdCertificate.ruleResponses

end
end Universality.Section5
