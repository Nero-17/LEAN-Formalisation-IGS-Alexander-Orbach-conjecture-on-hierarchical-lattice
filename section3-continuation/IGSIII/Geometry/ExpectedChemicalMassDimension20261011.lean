import IGSIII.Geometry.ChemicalDimensionComparison

set_option autoImplicit false

namespace IGSIII.Geometry
open Universality Universality.FiniteNetwork Filter Matrix
open scoped Topology

/-- Expected open-edge mass on the actual finite cluster, in arbitrary positive
logarithmic scale. Library generation `depth` is manuscript generation `depth+1`. -/
theorem actual_expected_chemical_mass_dimension20261011
    (rule : Rule) (classicalRule : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (growth : ℝ) (growthGreaterThanOne : 1 < growth) :
    Tendsto (fun depth : ℕ =>
      Real.log ((rule.generation depth).network.conditionalClusterMass parameter .connected) /
        (((depth + 1 : ℕ) : ℝ) * Real.log growth)) atTop
      (𝓝 (Real.log ((spectralRadius ℂ
        ((rule.network.massMatrix parameter).map Complex.ofReal)).toReal) / Real.log growth)) := by
  have ambientLogNonzero : Real.log
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast classicalRule.scale))
  have growthLogNonzero : Real.log growth ≠ 0 := ne_of_gt (Real.log_pos growthGreaterThanOne)
  convert (classicalRule.mass_dimension parameter positive belowOne fixedPoint .connected).mul_const
    (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) /
      Real.log growth) using 1
  · funext depth
    rw [rule.generation_terminal_distance (classicalRule.connected _), Nat.cast_pow, Real.log_pow]
    field_simp
  · congr 1
    field_simp

end IGSIII.Geometry
