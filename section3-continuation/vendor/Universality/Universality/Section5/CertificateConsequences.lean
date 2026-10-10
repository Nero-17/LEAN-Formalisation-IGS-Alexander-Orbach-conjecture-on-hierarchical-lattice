import Universality.Section5.CertificateRealisation
import Universality.Section5.GrowthDimensions
import Universality.Section5.DimensionSpan

/-!
Actual graph consequences of the exact allocation certificates. All numerical
certificate hypotheses remain explicit. Growth statements concern finite
generation observables; no physical exponent existence is assumed here.
-/

namespace Universality.Section5
noncomputable section
open Matrix FiniteNetwork Filter
open scoped Topology

theorem ExactAllocationCertificate.spectralRadius {depth base offset : ℕ}
    {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth base offset allocation) :
    _root_.spectralRadius ℂ
        (((allocatedExpression depth (allocationDecoration allocation)).rule.network.massMatrix
          (1 / 2)).map Complex.ofReal) = ENNReal.ofReal ((base : ℝ) ^ 219) := by
  exact spectralRadius_eq_of_positive_eigenvector _ certificateWeight _
    ((allocatedExpression depth (allocationDecoration allocation)).rule.network.massMatrix_nonneg
      (by norm_num) (by norm_num)) certificateWeight_pos (pow_nonneg (Nat.cast_nonneg base) 219)
    certificate.mass_response

theorem ExactAllocationCertificate.logarithmic_dimensions {depth base offset : ℕ}
    {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth base offset allocation) :
    Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.edges : ℝ) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target) =
      Real.log ((base : ℝ) ^ 232) / Real.log (base ^ 100 + offset : ℕ) ∧
    Real.log ((_root_.spectralRadius ℂ
        (((allocatedExpression depth (allocationDecoration allocation)).rule.network.massMatrix
          (1 / 2)).map Complex.ofReal)).toReal) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target) =
      Real.log ((base : ℝ) ^ 219) / Real.log (base ^ 100 + offset : ℕ) ∧
    Real.log (deriv
        (allocatedExpression depth (allocationDecoration allocation)).rule.network.reliability (1 / 2)) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target) =
      Real.log ((base : ℝ) ^ 70) / Real.log (base ^ 100 + offset : ℕ) := by
  obtain ⟨_, distance, volume, thermal⟩ := certificate.scalar_responses
  refine ⟨?_, ?_, ?_⟩
  · rw [distance, volume, Nat.cast_pow]
  · rw [certificate.spectralRadius,
      ENNReal.toReal_ofReal (pow_nonneg (Nat.cast_nonneg base) 219), distance]
  · rw [thermal, distance]

/-- Limits of actual generation observables, valid also for a nonzero distance offset. -/
theorem ExactAllocationCertificate.actual_growth_limits {depth base offset : ℕ}
    {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth base offset allocation) :
    (∀ n : ℕ, Real.log
        (((allocatedExpression depth (allocationDecoration allocation)).rule.generation n).edges : ℝ) /
        Real.log (((allocatedExpression depth (allocationDecoration allocation)).rule.generation n).network.fullGraph.dist
          ((allocatedExpression depth (allocationDecoration allocation)).rule.generation n).network.source
          ((allocatedExpression depth (allocationDecoration allocation)).rule.generation n).network.target) =
      Real.log ((base : ℝ) ^ 232) / Real.log (base ^ 100 + offset : ℕ)) ∧
    (∀ state : LiveState, Tendsto (fun n : ℕ => Real.log
        (((allocatedExpression depth (allocationDecoration allocation)).rule.generation n).network.conditionalClusterMass
          (1 / 2) state) /
        Real.log (((allocatedExpression depth (allocationDecoration allocation)).rule.generation n).network.fullGraph.dist
          ((allocatedExpression depth (allocationDecoration allocation)).rule.generation n).network.source
          ((allocatedExpression depth (allocationDecoration allocation)).rule.generation n).network.target))
      atTop (𝓝 (Real.log ((base : ℝ) ^ 219) / Real.log (base ^ 100 + offset : ℕ)))) ∧
    Tendsto ((allocatedExpression depth (allocationDecoration allocation)).rule.pivotalLogarithmicGrowth
      (1 / 2)) atTop (𝓝 (Real.log ((base : ℝ) ^ 70) / Real.log (base ^ 100 + offset : ℕ))) := by
  have formulas := (allocatedExpression depth (allocationDecoration allocation)).rule.finite_three_growth_formulas
    (1 / 2) (by norm_num) (by norm_num) certificate.scalar_responses.1
    certificate.classical.massAdmissible.symmetric certificate.classical.scale
  obtain ⟨ambient, mass, pivotal⟩ := certificate.logarithmic_dimensions
  simpa only [ambient, mass, pivotal] using formulas

/-- Two explicit primitive certificates yield infinitely many actual rules with
pairwise incommensurate scales and the three common finite-growth dimensions. -/
theorem exactCertificates_infinite_growth_family
    {firstDepth repeatedDepth : ℕ} {firstAllocation repeatedAllocation : List Bool → ℕ}
    (firstCertificate : ExactAllocationCertificate firstDepth 19 0 firstAllocation)
    (repeatedCertificate : ExactAllocationCertificate repeatedDepth 661 0 repeatedAllocation) :
    ∃ family : ℕ → Rule,
      Function.Injective family ∧ Set.Infinite (Set.range family) ∧
      (∀ index, RuleResponses (family index) (19 * 661 ^ index)) ∧
      (∀ i j, i ≠ j → ¬ ScaleCommensurate
        ((family i).network.fullGraph.dist (family i).network.source (family i).network.target)
        ((family j).network.fullGraph.dist (family j).network.source (family j).network.target)) ∧
      (∀ index,
        (∀ n : ℕ, Real.log (((family index).generation n).edges : ℝ) /
          Real.log (((family index).generation n).network.fullGraph.dist
            ((family index).generation n).network.source ((family index).generation n).network.target) =
          58 / 25) ∧
        (∀ state : LiveState, Tendsto (fun n : ℕ =>
          Real.log (((family index).generation n).network.conditionalClusterMass (1 / 2) state) /
            Real.log (((family index).generation n).network.fullGraph.dist
              ((family index).generation n).network.source ((family index).generation n).network.target))
          atTop (𝓝 (219 / 100))) ∧
        Tendsto ((family index).pivotalLogarithmicGrowth (1 / 2)) atTop (𝓝 (7 / 10))) := by
  refine ⟨compositionFamily
    (allocatedExpression firstDepth (allocationDecoration firstAllocation)).rule
    (allocatedExpression repeatedDepth (allocationDecoration repeatedAllocation)).rule,
    compositionFamily_injective firstCertificate.ruleResponses repeatedCertificate.ruleResponses,
    compositionFamily_infinite firstCertificate.ruleResponses repeatedCertificate.ruleResponses,
    ?_, ?_, ?_⟩
  · exact compositionFamily_responses firstCertificate.ruleResponses repeatedCertificate.ruleResponses
  · intro i j different
    exact compositionFamily_incommensurate firstCertificate.ruleResponses repeatedCertificate.ruleResponses different
  · intro index
    apply (compositionFamily_responses firstCertificate.ruleResponses repeatedCertificate.ruleResponses index).actual_growth_limits
    have positive : 0 < 661 ^ index := pow_pos (by norm_num) _
    omega

theorem ExactAllocationCertificate.shifted_dimensions {depth : ℕ}
    {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth 19 480 allocation) :
    Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.edges : ℝ) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target) =
      232 * (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) ∧
    Real.log ((_root_.spectralRadius ℂ
        (((allocatedExpression depth (allocationDecoration allocation)).rule.network.massMatrix
          (1 / 2)).map Complex.ofReal)).toReal) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target) =
      219 * (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) ∧
    Real.log (deriv
        (allocatedExpression depth (allocationDecoration allocation)).rule.network.reliability (1 / 2)) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target) =
      70 * (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) := by
  simpa only [Real.log_pow, Nat.cast_ofNat, mul_div_assoc] using certificate.logarithmic_dimensions

/-- The transcendence conclusion uses the accepted Gelfond--Schneider interface. -/
theorem ExactAllocationCertificate.shifted_dimensions_transcendental {depth : ℕ}
    {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth 19 480 allocation) :
    Transcendental ℚ
      (Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.edges : ℝ) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target)) ∧
    Transcendental ℚ
      (Real.log ((_root_.spectralRadius ℂ
          (((allocatedExpression depth (allocationDecoration allocation)).rule.network.massMatrix
            (1 / 2)).map Complex.ofReal)).toReal) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target)) ∧
    Transcendental ℚ
      (Real.log (deriv
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.reliability (1 / 2)) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target)) := by
  obtain ⟨ambient, mass, pivotal⟩ := certificate.logarithmic_dimensions
  rw [ambient, mass, pivotal]
  exact shifted_three_dimensions_transcendental

theorem ExactAllocationCertificate.shifted_dimensions_span_ranks {depth : ℕ}
    {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth 19 480 allocation) :
    Module.finrank ℚ (Submodule.span ℚ
      {Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.edges : ℝ) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target),
       Real.log ((_root_.spectralRadius ℂ
          (((allocatedExpression depth (allocationDecoration allocation)).rule.network.massMatrix
            (1 / 2)).map Complex.ofReal)).toReal) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target),
       Real.log (deriv
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.reliability (1 / 2)) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target)}) = 1 ∧
    Module.finrank ℚ (Submodule.span ℚ
      {1, Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.edges : ℝ) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target),
       Real.log ((_root_.spectralRadius ℂ
          (((allocatedExpression depth (allocationDecoration allocation)).rule.network.massMatrix
            (1 / 2)).map Complex.ofReal)).toReal) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target),
       Real.log (deriv
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.reliability (1 / 2)) /
        Real.log ((allocatedExpression depth (allocationDecoration allocation)).rule.network.fullGraph.dist
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
          (allocatedExpression depth (allocationDecoration allocation)).rule.network.target)}) = 2 := by
  obtain ⟨ambient, mass, pivotal⟩ := certificate.logarithmic_dimensions
  rw [ambient, mass, pivotal]
  exact ⟨shifted_dimensions_span_rank, shifted_dimensions_with_one_span_rank⟩

end
end Universality.Section5
