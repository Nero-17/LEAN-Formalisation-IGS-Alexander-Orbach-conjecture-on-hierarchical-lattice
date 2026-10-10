import IGSIII.Geometry.BoxDimensionLowerDefinition

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Filter
open scoped Topology NNReal ENNReal

theorem lowerBoxDimension_ge_of_eventual_geometric_packings {Space : Type*}
    [PseudoMetricSpace Space] [Nonempty Space]
    (baseRadius : ℝ≥0) (basePositive : 0 < baseRadius) (growth population : ℝ)
    (growthGreaterThanOne : 1 < growth) (populationGreaterThanOne : 1 < population)
    (count : ℕ → ℕ)
    (packings : ∀ depth, (count depth : ENat) ≤
      Metric.coveringNumber (baseRadius * growth.toNNReal⁻¹ ^ depth)
        (Set.univ : Set Space))
    (coefficient : ℝ) (coefficientPositive : 0 < coefficient)
    (eventualCount : ∀ᶠ depth in atTop, coefficient * population ^ depth ≤ (count depth : ℝ)) :
    ((Real.log population / Real.log growth : ℝ) : EReal) ≤ lowerBoxDimension Space := by
  have growthPositive := zero_lt_one.trans growthGreaterThanOne
  have populationPositive := zero_lt_one.trans populationGreaterThanOne
  let contraction : ℝ≥0 := ⟨growth⁻¹, inv_nonneg.mpr growthPositive.le⟩
  have contractionPositive : 0 < contraction := inv_pos.mpr growthPositive
  have contractionBelowOne : contraction < 1 := (inv_lt_one₀ growthPositive).mpr growthGreaterThanOne
  have exponentPositive : 0 < Real.log population / Real.log growth :=
    div_pos (Real.log_pos populationGreaterThanOne) (Real.log_pos growthGreaterThanOne)
  have inversePower : (growth⁻¹) ^ (Real.log population / Real.log growth) = population⁻¹ := by
    rw [Real.rpow_def_of_pos (inv_pos.mpr growthPositive), Real.log_inv]
    have algebra : -Real.log growth * (Real.log population / Real.log growth) = -Real.log population := by
      field_simp [(Real.log_pos growthGreaterThanOne).ne']
    rw [algebra, Real.exp_neg, Real.exp_log populationPositive]
  have supercritical : 1 ≤ population * (contraction : ℝ) ^ (Real.log population / Real.log growth) := by
    change 1 ≤ population * (growth⁻¹) ^ (Real.log population / Real.log growth)
    rw [inversePower, mul_inv_cancel₀ populationPositive.ne']
  obtain ⟨start, countBounds⟩ := eventually_atTop.mp eventualCount
  let smallerBase : ℝ≥0 := baseRadius * contraction ^ start
  have smallerBasePositive : 0 < smallerBase := mul_pos basePositive (pow_pos contractionPositive _)
  have shiftedPackings (depth : ℕ) : (count (start + depth) : ENat) ≤
      Metric.coveringNumber (smallerBase * contraction ^ depth) (Set.univ : Set Space) := by
    have contractionIdentity : contraction = growth.toNNReal⁻¹ := by
      apply NNReal.eq
      simp only [contraction, NNReal.coe_inv, Real.coe_toNNReal growth growthPositive.le]
      rfl
    simpa only [smallerBase, contractionIdentity, pow_add, mul_assoc] using packings (start + depth)
  have shiftedCounts (depth : ℕ) : (coefficient * population ^ start) * population ^ depth ≤ (count (start + depth) : ℝ) := by
    simpa only [pow_add, mul_assoc] using countBounds (start + depth) (by omega)
  apply lowerBoxDimension_ge_of_covering_power_lower_bound (Real.log population / Real.log growth)
    ((coefficient * population ^ start) * (smallerBase : ℝ) ^ (Real.log population / Real.log growth) *
      (contraction : ℝ) ^ (Real.log population / Real.log growth)) smallerBase (by positivity) smallerBasePositive
  intro radius radiusPositive radiusSmall finiteCover
  exact coveringNumber_power_lower_bound_of_geometric_packings smallerBase contraction smallerBasePositive
    contractionPositive contractionBelowOne population (coefficient * population ^ start)
    (Real.log population / Real.log growth) populationPositive (by positivity) exponentPositive.le supercritical
    (fun depth => count (start + depth)) shiftedPackings shiftedCounts radius radiusPositive radiusSmall finiteCover

end
end IGSIII.Geometry
