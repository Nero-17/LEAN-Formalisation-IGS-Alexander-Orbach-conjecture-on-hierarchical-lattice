import Universality.Percolation.PhysicalExponentClass
import Universality.Section5.GrowthDimensions
import Universality.Section5.CertificateRealisation
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
The four Section 5 exponents describe actual observables. The infinite-cluster
and finite-cluster probabilities come from the independently sampled uniform
root graph; the remaining limits use crossing length and the macroscopic
window average of the actual generation connectivity. The finite graph
response hypotheses imply every additional nonemptiness requirement.
-/

namespace Universality.Section5
noncomputable section

theorem RuleResponses.interior_nonempty {rule : Rule} {base : ℕ}
    (responses : RuleResponses rule base) : Nonempty rule.network.InteriorVertex := by
  obtain ⟨vertex, source_ne, target_ne⟩ := Fin.exists_ne_and_ne_of_two_lt
    rule.network.source rule.network.target responses.classical.vertices_gt_two
  exact ⟨⟨vertex, source_ne, target_ne⟩⟩

theorem RuleResponses.edges_neZero {rule : Rule} {base : ℕ}
    (responses : RuleResponses rule base) : NeZero rule.edges := by
  exact ⟨ne_of_gt (Nat.zero_lt_of_lt responses.classical.edges_gt_one)⟩

/-- The actual observable limits have the displayed four rational values. -/
theorem RuleResponses.hasCriticalExponents {rule : Rule} {base : ℕ}
    (responses : RuleResponses rule base) (base_gt_one : 1 < base) :
    letI : Nonempty rule.network.InteriorVertex := responses.interior_nonempty
    letI : NeZero rule.edges := responses.edges_neZero
    rule.HasCriticalExponents responses.classical.edges_gt_one (1 / 2)
      (13 / 70) (10 / 7) (219 / 13) (-3 / 50) := by
  letI : Nonempty rule.network.InteriorVertex := responses.interior_nonempty
  letI : NeZero rule.edges := responses.edges_neZero
  have observableLimits := responses.classical.hasCriticalExponents_in_dimensions
    (1 / 2) (by norm_num) (by norm_num) responses.fixed
  obtain ⟨ambient, mass, thermal⟩ := responses.dimensions base_gt_one
  rw [ambient, mass, thermal] at observableLimits
  norm_num at observableLimits ⊢
  exact observableLimits

/-- One half is the threshold for a positive actual infinite-cluster probability. -/
theorem RuleResponses.physical_infinite_cluster_positive_iff {rule : Rule} {base : ℕ}
    (responses : RuleResponses rule base) (p : ℝ) (nonnegative : 0 ≤ p) (at_most_one : p ≤ 1) :
    letI : Nonempty rule.network.InteriorVertex := responses.interior_nonempty
    letI : NeZero rule.edges := responses.edges_neZero
    0 < rule.physicalInfiniteClusterProbability responses.classical.edges_gt_one p ↔
      1 / 2 < p := by
  letI : Nonempty rule.network.InteriorVertex := responses.interior_nonempty
  letI : NeZero rule.edges := responses.edges_neZero
  exact Rule.Classical.physical_infinite_cluster_positive_iff rule responses.classical
    (1 / 2) p (by norm_num) (by norm_num) responses.fixed nonnegative at_most_one

/-- Rules with the Section 5 responses belong to the same observable class. -/
theorem RuleResponses.sameCriticalExponentUniversalityClass
    {first second : Rule} {firstBase secondBase : ℕ}
    (firstResponses : RuleResponses first firstBase)
    (secondResponses : RuleResponses second secondBase)
    (first_base_gt_one : 1 < firstBase) (second_base_gt_one : 1 < secondBase) :
    letI : Nonempty first.network.InteriorVertex := firstResponses.interior_nonempty
    letI : NeZero first.edges := firstResponses.edges_neZero
    letI : Nonempty second.network.InteriorVertex := secondResponses.interior_nonempty
    letI : NeZero second.edges := secondResponses.edges_neZero
    Rule.SameCriticalExponentUniversalityClass first second
      firstResponses.classical.edges_gt_one secondResponses.classical.edges_gt_one (1 / 2) (1 / 2) := by
  letI : Nonempty first.network.InteriorVertex := firstResponses.interior_nonempty
  letI : NeZero first.edges := firstResponses.edges_neZero
  letI : Nonempty second.network.InteriorVertex := secondResponses.interior_nonempty
  letI : NeZero second.edges := secondResponses.edges_neZero
  exact ⟨13 / 70, 10 / 7, 219 / 13, -3 / 50,
    firstResponses.hasCriticalExponents first_base_gt_one,
    secondResponses.hasCriticalExponents second_base_gt_one⟩

theorem ExactAllocationCertificate.interior_nonempty {depth base offset : ℕ}
    {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth base offset allocation) :
    Nonempty (allocatedExpression depth (allocationDecoration allocation)).rule.network.InteriorVertex := by
  obtain ⟨vertex, source_ne, target_ne⟩ := Fin.exists_ne_and_ne_of_two_lt
    (allocatedExpression depth (allocationDecoration allocation)).rule.network.source
    (allocatedExpression depth (allocationDecoration allocation)).rule.network.target
    certificate.classical.vertices_gt_two
  exact ⟨⟨vertex, source_ne, target_ne⟩⟩

theorem ExactAllocationCertificate.edges_neZero {depth base offset : ℕ}
    {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth base offset allocation) :
    NeZero (allocatedExpression depth (allocationDecoration allocation)).rule.edges := by
  exact ⟨ne_of_gt (Nat.zero_lt_of_lt certificate.classical.edges_gt_one)⟩

/-- A distance offset does not move the actual infinite-cluster threshold. -/
theorem ExactAllocationCertificate.physical_infinite_cluster_positive_iff
    {depth base offset : ℕ} {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth base offset allocation)
    (p : ℝ) (nonnegative : 0 ≤ p) (at_most_one : p ≤ 1) :
    letI : Nonempty (allocatedExpression depth (allocationDecoration allocation)).rule.network.InteriorVertex :=
      certificate.interior_nonempty
    letI : NeZero (allocatedExpression depth (allocationDecoration allocation)).rule.edges :=
      certificate.edges_neZero
    0 < (allocatedExpression depth (allocationDecoration allocation)).rule.physicalInfiniteClusterProbability
      certificate.classical.edges_gt_one p ↔ 1 / 2 < p := by
  letI : Nonempty (allocatedExpression depth (allocationDecoration allocation)).rule.network.InteriorVertex :=
    certificate.interior_nonempty
  letI : NeZero (allocatedExpression depth (allocationDecoration allocation)).rule.edges :=
    certificate.edges_neZero
  exact Rule.Classical.physical_infinite_cluster_positive_iff
    (allocatedExpression depth (allocationDecoration allocation)).rule certificate.classical
    (1 / 2) p (by norm_num) (by norm_num) certificate.scalar_responses.1 nonnegative at_most_one

end
end Universality.Section5
