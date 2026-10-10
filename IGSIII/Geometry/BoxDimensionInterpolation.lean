import IGSIII.Geometry.BoxDimensionPopulation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open scoped NNReal ENNReal
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology

/-- Geometric covers control every smaller radius, with the same exponent.
The covering number is the standard minimum over actual finite ball covers. -/
theorem coveringNumber_power_bound_of_geometric_covers {Space : Type*}
    [PseudoMetricSpace Space] (base_radius contraction : ℝ≥0)
    (base_positive : 0 < base_radius) (contraction_positive : 0 < contraction)
    (contraction_small : contraction < 1) (population coefficient exponent : ℝ)
    (population_nonnegative : 0 ≤ population) (coefficient_nonnegative : 0 ≤ coefficient)
    (exponent_nonnegative : 0 ≤ exponent)
    (subcritical : population * (contraction : ℝ) ^ exponent ≤ 1)
    (count : ℕ → ℕ)
    (covers : ∀ depth, Metric.coveringNumber (base_radius * contraction ^ depth) (Set.univ : Set Space) ≤ count depth)
    (count_bound : ∀ depth, (count depth : ℝ) ≤ coefficient * population ^ depth)
    (radius : ℝ≥0) (radius_positive : 0 < radius) (radius_small : radius ≤ base_radius) :
    Metric.coveringNumber radius (Set.univ : Set Space) ≠ ⊤ ∧
      ((Metric.coveringNumber radius (Set.univ : Set Space)).toNat : ℝ) * (radius : ℝ) ^ exponent ≤
        coefficient * population * (base_radius : ℝ) ^ exponent := by
  have base_real : 0 < (base_radius : ℝ) := base_positive
  have contraction_real : 0 < (contraction : ℝ) := contraction_positive
  obtain ⟨depth, lower, upper⟩ := exists_nat_pow_near_of_lt_one
    (div_pos (show 0 < (radius : ℝ) from radius_positive) base_real)
    ((div_le_one base_real).mpr (show (radius : ℝ) ≤ base_radius from radius_small))
    contraction_real (show (contraction : ℝ) < 1 from contraction_small)
  have mesh_smaller : base_radius * contraction ^ (depth + 1) ≤ radius := by
    change (base_radius : ℝ) * (contraction : ℝ) ^ (depth + 1) ≤ radius
    simpa only [mul_comm] using ((lt_div_iff₀ base_real).mp lower).le
  have count_at_radius := (Metric.coveringNumber_anti mesh_smaller (A := (Set.univ : Set Space))).trans
    (covers (depth + 1))
  refine ⟨ne_top_of_le_ne_top (ENat.coe_ne_top _) count_at_radius, ?_⟩
  have bound : ((Metric.coveringNumber radius (Set.univ : Set Space)).toNat : ℝ) ≤
      coefficient * population ^ (depth + 1) :=
    (Nat.cast_le.mpr (ENat.toNat_le_of_le_coe count_at_radius)).trans (count_bound (depth + 1))
  have radius_upper : (radius : ℝ) ≤ base_radius * (contraction : ℝ) ^ depth :=
    by simpa only [mul_comm] using (div_le_iff₀ base_real).mp upper
  have power_bound := Real.rpow_le_rpow (show 0 ≤ (radius : ℝ) from radius.coe_nonneg)
    radius_upper exponent_nonnegative
  have subcritical_power : (population * (contraction : ℝ) ^ exponent) ^ depth ≤ 1 :=
    pow_le_one₀ (mul_nonneg population_nonnegative (Real.rpow_nonneg contraction.coe_nonneg _)) subcritical
  calc
    _ ≤ (coefficient * population ^ (depth + 1)) *
        ((base_radius : ℝ) * (contraction : ℝ) ^ depth) ^ exponent :=
      mul_le_mul bound power_bound (Real.rpow_nonneg radius.coe_nonneg _) (by positivity)
    _ = coefficient * population * (base_radius : ℝ) ^ exponent *
        (population * (contraction : ℝ) ^ exponent) ^ depth := by
      rw [Real.mul_rpow base_radius.coe_nonneg (pow_nonneg contraction.coe_nonneg _),
        ← Real.rpow_pow_comm contraction.coe_nonneg, pow_succ, mul_pow]
      ring
    _ ≤ coefficient * population * (base_radius : ℝ) ^ exponent := by
      exact mul_le_of_le_one_right (by positivity) subcritical_power

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

/-- The actual chemical completion inherits a power bound for its covering
number from its proved birth nets and its actual retained vertex counts. -/
theorem actualChemicalSpace_covering_power_bound
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configuration_identity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (eta coefficient : ℝ) (start : ℕ) (eta_positive : 0 < eta) (eta_lt_one : eta < 1)
    (coefficient_positive : 0 < coefficient)
    (radius_bound : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) /
        scale ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length)
    (population population_coefficient exponent : ℝ) (population_positive : 0 < population)
    (population_coefficient_positive : 0 < population_coefficient)
    (exponent_nonnegative : 0 ≤ exponent) (subcritical : population * eta ^ exponent ≤ 1)
    (population_bound : ∀ depth,
      (Nat.card (RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) : ℝ) ≤
        population_coefficient * population ^ depth)
    (radius : ℝ≥0) (radius_positive : 0 < radius)
    (radius_small : (radius : ℝ) ≤ coefficient * eta ^ (start + 1)) :
    Metric.coveringNumber radius
      (Set.univ : Set (ActualChemicalSpace rule classical configuration coherent scale scale_positive
        limit_length nonnegative positive child_convergence)) ≠ ⊤ ∧
      ((Metric.coveringNumber radius
        (Set.univ : Set (ActualChemicalSpace rule classical configuration coherent scale scale_positive
          limit_length nonnegative positive child_convergence))).toNat : ℝ) * (radius : ℝ) ^ exponent ≤
        population_coefficient * population ^ (start + 1) * (coefficient * eta ^ (start + 1)) ^ exponent := by
  let base_radius : ℝ≥0 := ⟨coefficient * eta ^ (start + 1), by positivity⟩
  let contraction : ℝ≥0 := ⟨eta, eta_positive.le⟩
  have covers (depth : ℕ) : Metric.coveringNumber (base_radius * contraction ^ depth)
      (Set.univ : Set (ActualChemicalSpace rule classical configuration coherent scale scale_positive
        limit_length nonnegative positive child_convergence)) ≤
      Nat.card (RetainedSkeletonVertex (rule.generation (start + depth)).network (configuration (start + depth))) := by
    have actual := actualChemicalSpace_coveringNumber_le_retained_skeleton rule classical configuration coherent
      scale scale_positive limit_length nonnegative positive child_convergence marks configuration_identity eta coefficient start
      eta_positive.le coefficient_positive.le radius_bound (start + depth) (by omega)
    have radius_identity : base_radius * contraction ^ depth =
        ⟨coefficient * eta ^ (start + depth + 1), by positivity⟩ := by
      apply NNReal.eq
      change coefficient * eta ^ (start + 1) * eta ^ depth = coefficient * eta ^ (start + depth + 1)
      rw [show start + depth + 1 = (start + 1) + depth by omega, pow_add]
      ring
    rwa [radius_identity]
  have count_bound (depth : ℕ) :
      (Nat.card (RetainedSkeletonVertex (rule.generation (start + depth)).network (configuration (start + depth))) : ℝ) ≤
        (population_coefficient * population ^ start) * population ^ depth := by
    simpa only [pow_add, mul_assoc] using population_bound (start + depth)
  have interpolation := coveringNumber_power_bound_of_geometric_covers base_radius contraction
    (show 0 < base_radius by change 0 < coefficient * eta ^ (start + 1); positivity) eta_positive eta_lt_one population
    (population_coefficient * population ^ start) exponent population_positive.le (by positivity)
    exponent_nonnegative subcritical
    (fun depth => Nat.card (RetainedSkeletonVertex (rule.generation (start + depth)).network (configuration (start + depth))))
    covers count_bound radius radius_positive radius_small
  refine ⟨interpolation.1, ?_⟩
  have numerical := interpolation.2
  change _ ≤ population_coefficient * population ^ start * population *
    (coefficient * eta ^ (start + 1)) ^ exponent at numerical
  simpa only [pow_succ, mul_assoc] using numerical

end
end IGSIII.Geometry
