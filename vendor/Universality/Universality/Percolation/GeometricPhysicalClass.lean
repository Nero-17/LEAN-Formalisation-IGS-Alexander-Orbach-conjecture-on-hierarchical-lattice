import Universality.Geometry.GenerationHausdorffDimension
import Universality.Percolation.PhysicalExponentClass
import Universality.Examples.PhysicalClassCounterexample

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The finite real Hausdorff dimension of the actual generation completion.
The nonnegativity needed to recover a real number from `ENNReal.ofReal` follows
from the classical edge and scale inequalities. -/
theorem generationMetricSpace_dimH_toReal {rule : Rule} (h : rule.Classical) :
    (dimH (Set.univ : Set (GenerationMetricSpace h))).toReal =
      Real.log (rule.edges : ℝ) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) := by
  rw [generationMetricSpace_dimH_eq h]
  apply ENNReal.toReal_ofReal
  exact (div_pos (Real.log_pos (by exact_mod_cast h.edges_gt_one))
    (Real.log_pos (by exact_mod_cast h.scale))).le

/-- Equality of actual Hausdorff dimensions is equivalent to equality of the
edge/length growth fractions. Both fractions are nonnegative; no injectivity
of `ENNReal.ofReal` on arbitrary real numbers is used. -/
theorem generationMetricSpace_dimH_eq_iff {first second : Rule}
    (hfirst : first.Classical) (hsecond : second.Classical) :
    dimH (Set.univ : Set (GenerationMetricSpace hfirst)) =
      dimH (Set.univ : Set (GenerationMetricSpace hsecond)) ↔
      Real.log (first.edges : ℝ) /
          Real.log (first.network.fullGraph.dist first.network.source first.network.target : ℝ) =
        Real.log (second.edges : ℝ) /
          Real.log (second.network.fullGraph.dist second.network.source second.network.target : ℝ) := by
  constructor
  · intro hequal
    have hreal := congrArg ENNReal.toReal hequal
    simpa only [generationMetricSpace_dimH_toReal] using hreal
  · intro hequal
    rw [generationMetricSpace_dimH_eq hfirst, generationMetricSpace_dimH_eq hsecond, hequal]

variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

/-- Classification by the actual ambient Hausdorff dimension and the two
explicit critical growth dimensions. -/
theorem Classical.same_critical_exponent_class_iff_geometric_dimensions
    {first second : Rule}
    [Nonempty first.network.InteriorVertex] [NeZero first.edges]
    [Nonempty second.network.InteriorVertex] [NeZero second.edges]
    (hfirst : first.Classical) (hsecond : second.Classical)
    (criticalFirst criticalSecond : ℝ)
    (hcFirst : 0 < criticalFirst) (hcFirst' : criticalFirst < 1)
    (hfixedFirst : first.network.reliability criticalFirst = criticalFirst)
    (hcSecond : 0 < criticalSecond) (hcSecond' : criticalSecond < 1)
    (hfixedSecond : second.network.reliability criticalSecond = criticalSecond) :
    SameCriticalExponentUniversalityClass first second hfirst.edges_gt_one hsecond.edges_gt_one
      criticalFirst criticalSecond ↔
      dimH (Set.univ : Set (GenerationMetricSpace hfirst)) =
          dimH (Set.univ : Set (GenerationMetricSpace hsecond)) ∧
      Real.log ((spectralRadius ℂ ((first.network.massMatrix criticalFirst).map Complex.ofReal)).toReal) /
          Real.log (first.network.fullGraph.dist first.network.source first.network.target : ℝ) =
        Real.log ((spectralRadius ℂ ((second.network.massMatrix criticalSecond).map Complex.ofReal)).toReal) /
          Real.log (second.network.fullGraph.dist second.network.source second.network.target : ℝ) ∧
      Real.log (deriv first.network.reliability criticalFirst) /
          Real.log (first.network.fullGraph.dist first.network.source first.network.target : ℝ) =
        Real.log (deriv second.network.reliability criticalSecond) /
          Real.log (second.network.fullGraph.dist second.network.source second.network.target : ℝ) := by
  rw [generationMetricSpace_dimH_eq_iff hfirst hsecond]
  exact hfirst.same_critical_exponent_class_iff_dimensions hsecond
    criticalFirst criticalSecond hcFirst hcFirst' hfixedFirst hcSecond hcSecond' hfixedSecond

/-- The four actual observable exponents, with the ambient term expressed by
the Hausdorff dimension of the actual compact generation metric space. -/
theorem Classical.hasCriticalExponents_with_hausdorff_dimension {rule : Rule}
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges] (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    rule.HasCriticalExponents h.edges_gt_one critical
      (((dimH (Set.univ : Set (GenerationMetricSpace h))).toReal -
        Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) /
        (Real.log (deriv rule.network.reliability critical) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)))
      (1 / (Real.log (deriv rule.network.reliability critical) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)))
      ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)) /
        ((dimH (Set.univ : Set (GenerationMetricSpace h))).toReal -
          Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
            Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)))
      (2 + (dimH (Set.univ : Set (GenerationMetricSpace h))).toReal -
        2 * (Real.log ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) /
          Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ))) := by
  rw [generationMetricSpace_dimH_toReal h]
  exact h.hasCriticalExponents_in_dimensions critical hc hc' hfixed

end
end Universality.Rule

namespace Universality
noncomputable section
open Rule
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

/-- Equal Hausdorff dimensions of the actual compact generation limits do not
determine the class of the four actual percolation exponents. -/
theorem hausdorff_dimension_does_not_classify_physical_exponents :
    dimH (Set.univ : Set (GenerationMetricSpace groupedRule_classical)) =
      dimH (Set.univ : Set (GenerationMetricSpace alternatingRule_classical)) ∧
    ¬ SameCriticalExponentUniversalityClass groupedRule alternatingRule
      groupedRule_classical.edges_gt_one alternatingRule_classical.edges_gt_one (1/2) (1/2) := by
  refine ⟨?_, reordered_physical_exponent_classes_differ⟩
  apply (generationMetricSpace_dimH_eq_iff groupedRule_classical alternatingRule_classical).mpr
  exact ambient_dimension_does_not_classify_physical_exponents.1

end
end Universality
