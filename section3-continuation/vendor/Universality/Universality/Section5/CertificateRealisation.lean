import Universality.Section5.CertificateScalarBridge
import Universality.Section5.ActualAllocationMass
import Universality.Graph.Section5AllocationDistance
import Universality.Section5.CompositionFamily
import Universality.Section5.CertificateMassBridge

namespace Universality.Section5
noncomputable section
open FiniteNetwork Matrix

/-- The four exact finite identities, together with pointwise allocation capacity.
The offset is zero for the rational examples and 480 for the shifted example. -/
structure ExactAllocationCertificate (depth base offset : ℕ) (allocation : List Bool → ℕ) : Prop where
  positive_depth : 0 < depth
  capacity : ∀ word ∈ binaryWords depth, allocation word ≤ 2 ^ zeroCount word
  distance : 2 ^ depth + allocation (List.replicate depth false) = base ^ 100 + offset
  volume : 5 ^ depth + 4 * ((binaryWords depth).map
    (fun word => allocation word * 2 ^ zeroCount word)).sum = base ^ 232
  thermal : 8 ^ (depth + 1) * base ^ 70 = 8 * 13 ^ depth + 5 * ((binaryWords depth).map
    (fun word => allocation word * 6 ^ zeroCount word)).sum
  mass : allocationMassNumerator depth allocation *ᵥ
      (![55, 23] : Fin 2 → ℤ) =
        ((16 : ℤ) ^ (depth + 1) * (base : ℤ) ^ 219) • ![55, 23]

theorem ExactAllocationCertificate.classical {depth base offset : ℕ} {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth base offset allocation) :
    (allocatedExpression depth (allocationDecoration allocation)).rule.Classical :=
  allocatedExpression_classical _ _ certificate.positive_depth

theorem ExactAllocationCertificate.scalar_responses {depth base offset : ℕ}
    {allocation : List Bool → ℕ} (certificate : ExactAllocationCertificate depth base offset allocation) :
    (allocatedExpression depth (allocationDecoration allocation)).rule.network.reliability (1 / 2) = 1 / 2 ∧
    (allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
      (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
      (allocatedExpression depth (allocationDecoration allocation)).rule.network.target = base ^ 100 + offset ∧
    (allocatedExpression depth (allocationDecoration allocation)).rule.edges = base ^ 232 ∧
    deriv (allocatedExpression depth (allocationDecoration allocation)).rule.network.reliability (1 / 2) =
      (base : ℝ) ^ 70 := by
  refine ⟨allocatedExpression_fixed_half _ _, ?_, ?_, ?_⟩
  · rw [allocation_distance _ _ certificate.capacity]
    exact certificate.distance
  · rw [allocation_edges _ _ certificate.capacity]
    exact certificate.volume
  · exact allocation_derivative_of_certificate depth base allocation certificate.capacity certificate.thermal

theorem ExactAllocationCertificate.mass_response {depth base offset : ℕ}
    {allocation : List Bool → ℕ} (certificate : ExactAllocationCertificate depth base offset allocation) :
    (allocatedExpression depth (allocationDecoration allocation)).rule.network.massMatrix (1 / 2) *ᵥ
      certificateWeight = (base : ℝ) ^ 219 • certificateWeight :=
  allocation_massMatrix_eigenvector depth base allocation certificate.capacity certificate.mass

theorem ExactAllocationCertificate.ruleResponses {depth base : ℕ}
    {allocation : List Bool → ℕ} (certificate : ExactAllocationCertificate depth base 0 allocation) :
    RuleResponses (allocatedExpression depth (allocationDecoration allocation)).rule base := by
  obtain ⟨fixed, distance, volume, thermal⟩ := certificate.scalar_responses
  exact ⟨certificate.classical, fixed, by simpa using distance, volume, thermal, certificate.mass_response⟩

theorem ExactAllocationCertificate.exists_rule {depth base : ℕ}
    {allocation : List Bool → ℕ} (certificate : ExactAllocationCertificate depth base 0 allocation) :
    ∃ rule : Rule, RuleResponses rule base :=
  ⟨(allocatedExpression depth (allocationDecoration allocation)).rule, certificate.ruleResponses⟩

end
end Universality.Section5
