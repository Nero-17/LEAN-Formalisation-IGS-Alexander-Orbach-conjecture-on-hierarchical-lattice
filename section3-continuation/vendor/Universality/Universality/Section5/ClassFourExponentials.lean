import Universality.Arithmetic.GraphCriticalDimensions
import Universality.Percolation.PhysicalExponentClass
import Universality.Section5.FourExponentialsObstruction

/-! The discussion's conditional commensurability claim for actual physical
classes. Algebraicity is proved from the finite classical rules, not assumed.
The four-exponentials conjecture remains an explicit proposition parameter. -/

namespace Universality.Rule
noncomputable section

theorem Classical.criticalDimension_transcendental_of_irrational {rule : Rule}
    (classical : rule.Classical) (critical : ℝ)
    (positive : 0 < critical) (below_one : critical < 1)
    (fixed : rule.network.reliability critical = critical) (index : Fin 3)
    (irrational : Irrational (rule.criticalDimensions critical index)) :
    Transcendental ℚ (rule.criticalDimensions critical index) := by
  have logarithmic_identity :
      Real.log (Real.exp
        (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) *
          rule.criticalDimensions critical index)) /
        Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) =
          rule.criticalDimensions critical index := by
    rw [Real.log_exp]
    exact mul_div_cancel_left₀ _
      (ne_of_gt (Real.log_pos (by exact_mod_cast classical.scale)))
  have transcendence := Section4.logarithmic_dimension_transcendental
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)
    (Real.exp (Real.log (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) *
      rule.criticalDimensions critical index))
    (by exact_mod_cast classical.scale) (Real.exp_pos _)
    (isAlgebraic_nat _) (classical.exp_log_scale_criticalDimensions_algebraic
      critical positive below_one fixed index)
    (by rwa [logarithmic_identity])
  rwa [logarithmic_identity] at transcendence

variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
variable {first second : Rule}
variable [Nonempty first.network.InteriorVertex] [NeZero first.edges]
variable [Nonempty second.network.InteriorVertex] [NeZero second.edges]

theorem Classical.commensurate_of_fourExponentials_physicalClass
    (first_classical : first.Classical) (second_classical : second.Classical)
    (conjecture : Section5.FourExponentialsReal)
    (firstCritical secondCritical : ℝ)
    (first_positive : 0 < firstCritical) (first_below_one : firstCritical < 1)
    (second_positive : 0 < secondCritical) (second_below_one : secondCritical < 1)
    (first_fixed : first.network.reliability firstCritical = firstCritical)
    (second_fixed : second.network.reliability secondCritical = secondCritical)
    (same_class : SameCriticalExponentUniversalityClass first second
      first_classical.edges_gt_one second_classical.edges_gt_one firstCritical secondCritical)
    (irrational : ∃ index : Fin 3, Irrational (first.criticalDimensions firstCritical index)) :
    ScaleCommensurate
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target) := by
  have dimensions_equal : first.criticalDimensions firstCritical =
      second.criticalDimensions secondCritical := by
    obtain ⟨ambient, mass, pivotal⟩ :=
      (first_classical.same_critical_exponent_class_iff_dimensions second_classical
        firstCritical secondCritical first_positive first_below_one first_fixed
        second_positive second_below_one second_fixed).mp same_class
    funext index
    fin_cases index
    · exact ambient
    · exact mass
    · exact pivotal
  obtain ⟨index, dimension_irrational⟩ := irrational
  apply Section5.four_exponentials_commensurability_of_common_irrational_dimension
    conjecture first_classical.scale second_classical.scale
    (Real.exp_pos _) (Real.exp_pos _)
    (first_classical.exp_log_scale_criticalDimensions_algebraic firstCritical
      first_positive first_below_one first_fixed index)
    (second_classical.exp_log_scale_criticalDimensions_algebraic secondCritical
      second_positive second_below_one second_fixed index)
    (dimension := first.criticalDimensions firstCritical index)
  · rw [Real.log_exp]
    exact mul_div_cancel_left₀ _ (ne_of_gt (Real.log_pos (by exact_mod_cast first_classical.scale)))
  · rw [Real.log_exp, ← dimensions_equal]
    exact mul_div_cancel_left₀ _ (ne_of_gt (Real.log_pos (by exact_mod_cast second_classical.scale)))
  · exact dimension_irrational

theorem Classical.incommensurate_physicalClass_obstructs_fourExponentials
    (first_classical : first.Classical) (second_classical : second.Classical)
    (firstCritical secondCritical : ℝ)
    (first_positive : 0 < firstCritical) (first_below_one : firstCritical < 1)
    (second_positive : 0 < secondCritical) (second_below_one : secondCritical < 1)
    (first_fixed : first.network.reliability firstCritical = firstCritical)
    (second_fixed : second.network.reliability secondCritical = secondCritical)
    (same_class : SameCriticalExponentUniversalityClass first second
      first_classical.edges_gt_one second_classical.edges_gt_one firstCritical secondCritical)
    (irrational : ∃ index : Fin 3, Irrational (first.criticalDimensions firstCritical index))
    (incommensurate : ¬ ScaleCommensurate
      (first.network.fullGraph.dist first.network.source first.network.target)
      (second.network.fullGraph.dist second.network.source second.network.target)) :
    ¬ Section5.FourExponentialsReal := by
  intro conjecture
  exact incommensurate (first_classical.commensurate_of_fourExponentials_physicalClass
    second_classical conjecture firstCritical secondCritical first_positive first_below_one
    second_positive second_below_one first_fixed second_fixed same_class irrational)

end
end Universality.Rule

#print axioms Universality.Rule.Classical.commensurate_of_fourExponentials_physicalClass
#print axioms Universality.Rule.Classical.incommensurate_physicalClass_obstructs_fourExponentials
#print axioms Universality.Rule.Classical.criticalDimension_transcendental_of_irrational
