import Universality.Percolation.PhysicalExponentDefinition
import Universality.Percolation.ClassicalCriticalPoint

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Filter
open scoped Topology
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
variable {rule : Rule} [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]

theorem Classical.critical_dimension_gap_positive (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1) :
    0 < Real.log (rule.edges : ℝ) /
      Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) -
      Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) := by
  have hgrowth : 0 < (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal :=
    lt_of_le_of_lt (Nat.cast_nonneg _) (h.terminal_degree_spectral_bounds critical hc hc').2.1
  have hgap := Real.log_lt_log hgrowth (h.mass_spectralRadius_lt_edges critical hc hc')
  rw [← sub_div]
  exact div_pos (sub_pos.mpr hgap) (Real.log_pos (by exact_mod_cast h.scale))

theorem Classical.hasCriticalExponents_in_dimensions (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    rule.HasCriticalExponents h.edges_gt_one critical
      ((Real.log (rule.edges : ℝ) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) /
        (Real.log (deriv rule.network.reliability critical) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)))
      (1 / (Real.log (deriv rule.network.reliability critical) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)))
      ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) /
        (Real.log (rule.edges : ℝ) /
            Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) -
          Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
            Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)))
      (2 + Real.log (rule.edges : ℝ) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) -
        2 * (Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ))) := by
  have hscale : Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast h.scale)).ne'
  have hthermal : Real.log (deriv rule.network.reliability critical) ≠ 0 :=
    (Real.log_pos (rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale)).ne'
  have hgrowth : 0 < (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal :=
    lt_of_le_of_lt (Nat.cast_nonneg _) (h.terminal_degree_spectral_bounds critical hc hc').2.1
  have hgap : Real.log (rule.edges : ℝ) -
      Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ≠ 0 :=
    (sub_pos.mpr (Real.log_lt_log hgrowth (h.mass_spectralRadius_lt_edges critical hc hc'))).ne'
  convert h.hasCriticalExponents critical hc hc' hfixed using 1 <;>
    field_simp [hscale, hthermal, hgap] <;> ring

end
end Universality.Rule
