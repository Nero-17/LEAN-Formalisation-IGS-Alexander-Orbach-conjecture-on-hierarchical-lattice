import Universality.Section5.SeedCertificates
import Universality.Section5.HausdorffDimensions
import Universality.Section5.PhysicalExponents
import Universality.Section5.PhysicalSeed19
import Universality.Section5.PhysicalSeed739
import Universality.Section5.PhysicalShifted19

/-!
Concrete growth, metric dimension, physical exponents, and rational-span consequences of the seeds.
These declarations have no certificate hypotheses: their proof dependencies are
the four exact seed certificates imported above. The physical limits refer to
the independently sampled uniform-root graph and the actual generation observables.
-/

namespace Universality.Section5
noncomputable section
open FiniteNetwork Filter
open scoped Topology

theorem certifiedRule661_hasCriticalExponents :
    letI : Nonempty certifiedRule661.network.InteriorVertex := certifiedRule661_responses.interior_nonempty
    letI : NeZero certifiedRule661.edges := certifiedRule661_responses.edges_neZero
    certifiedRule661.HasCriticalExponents certifiedRule661_responses.classical.edges_gt_one
      (1 / 2) (13 / 70) (10 / 7) (219 / 13) (-3 / 50) :=
  certifiedRule661_responses.hasCriticalExponents (by norm_num)

theorem certifiedRule19_and661_sameCriticalExponentUniversalityClass :
    letI : Nonempty certifiedRule19.network.InteriorVertex := certifiedRule19_responses.interior_nonempty
    letI : NeZero certifiedRule19.edges := certifiedRule19_responses.edges_neZero
    letI : Nonempty certifiedRule661.network.InteriorVertex := certifiedRule661_responses.interior_nonempty
    letI : NeZero certifiedRule661.edges := certifiedRule661_responses.edges_neZero
    Rule.SameCriticalExponentUniversalityClass certifiedRule19 certifiedRule661
      certifiedRule19_responses.classical.edges_gt_one certifiedRule661_responses.classical.edges_gt_one
      (1 / 2) (1 / 2) :=
  certifiedRule19_responses.sameCriticalExponentUniversalityClass certifiedRule661_responses
    (by norm_num) (by norm_num)

theorem certifiedFamily_actual_growth_limits (index : ℕ) :
    (∀ n : ℕ, Real.log (((certifiedFamily index).generation n).edges : ℝ) /
      Real.log (((certifiedFamily index).generation n).network.fullGraph.dist
        ((certifiedFamily index).generation n).network.source
        ((certifiedFamily index).generation n).network.target) = 58 / 25) ∧
    (∀ state : LiveState, Tendsto (fun n : ℕ =>
      Real.log (((certifiedFamily index).generation n).network.conditionalClusterMass (1 / 2) state) /
        Real.log (((certifiedFamily index).generation n).network.fullGraph.dist
          ((certifiedFamily index).generation n).network.source
          ((certifiedFamily index).generation n).network.target))
      atTop (𝓝 (219 / 100))) ∧
    Tendsto ((certifiedFamily index).pivotalLogarithmicGrowth (1 / 2))
      atTop (𝓝 (7 / 10)) := by
  apply (certifiedFamily_responses index).actual_growth_limits
  have positive : 0 < 661 ^ index := pow_pos (by norm_num) _
  omega

theorem certifiedFamily_hausdorff_dimension (index : ℕ) :
    dimH (Set.univ : Set (Rule.GenerationMetricSpace
      (certifiedFamily_responses index).classical)) = ENNReal.ofReal (58 / 25) := by
  apply (certifiedFamily_responses index).hausdorff_dimension
  have positive : 0 < 661 ^ index := pow_pos (by norm_num) _
  omega

theorem certifiedFamily_hasCriticalExponents (index : ℕ) :
    letI : Nonempty (certifiedFamily index).network.InteriorVertex :=
      (certifiedFamily_responses index).interior_nonempty
    letI : NeZero (certifiedFamily index).edges := (certifiedFamily_responses index).edges_neZero
    (certifiedFamily index).HasCriticalExponents (certifiedFamily_responses index).classical.edges_gt_one
      (1 / 2) (13 / 70) (10 / 7) (219 / 13) (-3 / 50) := by
  apply (certifiedFamily_responses index).hasCriticalExponents
  have positive : 0 < 661 ^ index := pow_pos (by norm_num) _
  omega

theorem certifiedFamily_physical_infinite_cluster_positive_iff
    (index : ℕ) (p : ℝ) (nonnegative : 0 ≤ p) (at_most_one : p ≤ 1) :
    letI : Nonempty (certifiedFamily index).network.InteriorVertex :=
      (certifiedFamily_responses index).interior_nonempty
    letI : NeZero (certifiedFamily index).edges := (certifiedFamily_responses index).edges_neZero
    0 < (certifiedFamily index).physicalInfiniteClusterProbability
      (certifiedFamily_responses index).classical.edges_gt_one p ↔ 1 / 2 < p :=
  (certifiedFamily_responses index).physical_infinite_cluster_positive_iff p nonnegative at_most_one

theorem certifiedFamily_sameCriticalExponentUniversalityClass (first second : ℕ) :
    letI : Nonempty (certifiedFamily first).network.InteriorVertex :=
      (certifiedFamily_responses first).interior_nonempty
    letI : NeZero (certifiedFamily first).edges := (certifiedFamily_responses first).edges_neZero
    letI : Nonempty (certifiedFamily second).network.InteriorVertex :=
      (certifiedFamily_responses second).interior_nonempty
    letI : NeZero (certifiedFamily second).edges := (certifiedFamily_responses second).edges_neZero
    Rule.SameCriticalExponentUniversalityClass (certifiedFamily first) (certifiedFamily second)
      (certifiedFamily_responses first).classical.edges_gt_one
      (certifiedFamily_responses second).classical.edges_gt_one (1 / 2) (1 / 2) := by
  apply (certifiedFamily_responses first).sameCriticalExponentUniversalityClass
    (certifiedFamily_responses second)
  · have positive : 0 < 661 ^ first := pow_pos (by norm_num) _
    omega
  · have positive : 0 < 661 ^ second := pow_pos (by norm_num) _
    omega

theorem certifiedRuleShifted19_hausdorff_dimension_transcendental :
    Transcendental ℚ (dimH (Set.univ : Set
      (Rule.GenerationMetricSpace certifiedRuleShifted19_classical))).toReal :=
  exactAllocationShifted19.shifted_hausdorff_dimension_transcendental

theorem certifiedRuleShifted19_span_ranks :
    Module.finrank ℚ (Submodule.span ℚ
      {Real.log (certifiedRuleShifted19.edges : ℝ) /
        Real.log (certifiedRuleShifted19.network.fullGraph.dist
          certifiedRuleShifted19.network.source certifiedRuleShifted19.network.target),
       Real.log ((_root_.spectralRadius ℂ
          ((certifiedRuleShifted19.network.massMatrix (1 / 2)).map Complex.ofReal)).toReal) /
        Real.log (certifiedRuleShifted19.network.fullGraph.dist
          certifiedRuleShifted19.network.source certifiedRuleShifted19.network.target),
       Real.log (deriv certifiedRuleShifted19.network.reliability (1 / 2)) /
        Real.log (certifiedRuleShifted19.network.fullGraph.dist
          certifiedRuleShifted19.network.source certifiedRuleShifted19.network.target)}) = 1 ∧
    Module.finrank ℚ (Submodule.span ℚ
      {1, Real.log (certifiedRuleShifted19.edges : ℝ) /
        Real.log (certifiedRuleShifted19.network.fullGraph.dist
          certifiedRuleShifted19.network.source certifiedRuleShifted19.network.target),
       Real.log ((_root_.spectralRadius ℂ
          ((certifiedRuleShifted19.network.massMatrix (1 / 2)).map Complex.ofReal)).toReal) /
        Real.log (certifiedRuleShifted19.network.fullGraph.dist
          certifiedRuleShifted19.network.source certifiedRuleShifted19.network.target),
       Real.log (deriv certifiedRuleShifted19.network.reliability (1 / 2)) /
        Real.log (certifiedRuleShifted19.network.fullGraph.dist
          certifiedRuleShifted19.network.source certifiedRuleShifted19.network.target)}) = 2 :=
  exactAllocationShifted19.shifted_dimensions_span_ranks

end
end Universality.Section5
