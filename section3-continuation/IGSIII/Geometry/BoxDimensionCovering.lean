import IGSIII.Geometry.ActualChemicalNets
import Mathlib.Topology.MetricSpace.CoveringNumbers

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology NNReal ENNReal

/-- A finite family of actual centres bounds the usual internal covering
number. Repeated centres do not increase the bound. -/
theorem coveringNumber_le_finite_centres {Space Index : Type*}
    [PseudoMetricSpace Space] [Fintype Index] (centres : Index → Space)
    (radius : ℝ≥0) (cover : ∀ point, ∃ index, dist point (centres index) ≤ radius) :
    Metric.coveringNumber radius (Set.univ : Set Space) ≤ Fintype.card Index := by
  classical
  have net : Metric.IsCover radius (Set.univ : Set Space) (Set.range centres) := by
    apply Metric.IsCover.of_subset_iUnion_closedBall
    intro point _
    obtain ⟨index, close⟩ := cover point
    exact Set.mem_iUnion.mpr ⟨centres index, Set.mem_iUnion.mpr
      ⟨⟨index, rfl⟩, Metric.mem_closedBall.mpr close⟩⟩
  apply (net.coveringNumber_le_encard (Set.subset_univ _)).trans
  simpa only [Set.image_univ, Set.encard_univ, ENat.card_eq_coe_fintype_card] using
    Set.encard_image_le centres (Set.univ : Set Index)

/-- A separated family forces at least one distinct covering centre for each
member. The strict inequality is the one in Mathlib's packing convention. -/
theorem finite_separated_le_coveringNumber {Space Index : Type*}
    [PseudoMetricSpace Space] [Fintype Index] (points : Index → Space)
    (radius : ℝ≥0) (separated : ∀ first second, first ≠ second →
      2 * (radius : ℝ) < dist (points first) (points second)) :
    Fintype.card Index ≤ Metric.coveringNumber radius (Set.univ : Set Space) := by
  classical
  have injective : Function.Injective points := by
    intro first second equal
    by_contra distinct
    have bound := separated first second distinct
    rw [equal, dist_self] at bound
    exact (not_lt_of_ge (mul_nonneg (by norm_num) radius.coe_nonneg)) bound
  have separation : Metric.IsSeparated (↑(2 * radius) : ℝ≥0∞) (Set.range points) := by
    intro first first_member second second_member distinct
    obtain ⟨first_index, rfl⟩ := first_member
    obtain ⟨second_index, rfl⟩ := second_member
    have bound := separated first_index second_index (fun equal => distinct (congrArg points equal))
    rw [edist_dist, ENNReal.coe_lt_ofReal]
    simpa only [NNReal.coe_mul, NNReal.coe_ofNat] using bound
  calc
    (Fintype.card Index : ℕ∞) ≤ (Set.range points).encard := by
      simpa only [ENat.card_eq_coe_fintype_card] using injective.encard_range
    _ ≤ Metric.packingNumber (2 * radius) (Set.univ : Set Space) :=
      separation.encard_le_packingNumber (Set.subset_univ _)
    _ ≤ Metric.externalCoveringNumber radius (Set.univ : Set Space) :=
      Metric.packingNumber_two_mul_le_externalCoveringNumber radius _
    _ ≤ Metric.coveringNumber radius (Set.univ : Set Space) :=
      Metric.externalCoveringNumber_le_coveringNumber _ _

variable (rule : Rule) (classical : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (scale : ℝ) (scale_positive : 0 < scale)
variable (limit_length : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ limit_length depth edge)
variable (positive : ∀ depth edge, configuration depth edge = true → 0 < limit_length depth edge)
variable (child_convergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (limit_length coarse edge)))

/-- The actual retained birth skeleton covers the actual completed chemical
space, with its proved mesh. No cover of the limiting space is an input. -/
theorem actualChemicalSpace_coveringNumber_le_retained_skeleton
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configuration_identity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (eta coefficient : ℝ) (start : ℕ) (eta_nonnegative : 0 ≤ eta) (coefficient_nonnegative : 0 ≤ coefficient)
    (radius_bound : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) /
        scale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length)
    (age : ℕ) (beyond : start ≤ age + 1) :
    Metric.coveringNumber
      ⟨coefficient * eta ^ (age + 1), mul_nonneg coefficient_nonnegative (pow_nonneg eta_nonnegative _)⟩
      (Set.univ : Set (ActualChemicalSpace rule classical configuration coherent scale scale_positive
        limit_length nonnegative positive child_convergence)) ≤
      Nat.card (RetainedSkeletonVertex (rule.generation age).network (configuration age)) := by
  classical
  letI := Fintype.ofFinite (RetainedSkeletonVertex (rule.generation age).network (configuration age))
  rw [Nat.card_eq_fintype_card]
  apply coveringNumber_le_finite_centres
    (actualChemicalVertex rule classical configuration coherent scale scale_positive
      limit_length nonnegative positive child_convergence age)
  exact actualChemicalSpace_near_birth_skeleton rule classical configuration coherent scale scale_positive
    limit_length nonnegative positive child_convergence marks configuration_identity eta coefficient start
    eta_nonnegative coefficient_nonnegative radius_bound age beyond

end
end IGSIII.Geometry
