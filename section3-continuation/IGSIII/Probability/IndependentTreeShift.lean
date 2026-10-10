import IGSIII.Chemical.SubstitutionPaths.IndependentInnovations
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! Measure-preserving descendant shifts on the actual C/N innovation space. -/

set_option autoImplicit false

namespace IGSIII.Probability

open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Chemical.Substitution
open scoped ENNReal

def innovationTreeShift (rule : Rule) (addressPrefix : List (Fin rule.edges))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    (List (Fin rule.edges) × Bool) → Configuration rule.edges :=
  fun coordinate => marks (addressPrefix ++ coordinate.1, coordinate.2)

theorem innovationTreeShift_measurable (rule : Rule) (addressPrefix : List (Fin rule.edges)) :
    Measurable (innovationTreeShift rule addressPrefix) := by
  exact measurable_pi_lambda _ (fun coordinate => measurable_pi_apply (addressPrefix ++ coordinate.1, coordinate.2))

theorem innovationTreeShift_preserving (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (addressPrefix : List (Fin rule.edges)) :
    MeasurePreserving (innovationTreeShift rule addressPrefix)
      (independentInnovationLaw rule p positive belowOne fixedPoint)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  letI : ∀ coordinate : List (Fin rule.edges) × Bool,
      IsProbabilityMeasure (Rule.ConfigurationHistory.law rule p positive belowOne fixedPoint coordinate.2 0) :=
    fun coordinate => Rule.ConfigurationHistory.law_probability rule p positive belowOne fixedPoint coordinate.2 0
  refine ⟨innovationTreeShift_measurable rule addressPrefix, ?_⟩
  have injective : Function.Injective
      (fun coordinate : List (Fin rule.edges) × Bool => (addressPrefix ++ coordinate.1, coordinate.2)) := by
    intro first second equality
    apply Prod.ext
    · exact List.append_cancel_left (congrArg Prod.fst equality)
    · change first.2 = second.2
      exact (Prod.mk.inj equality).2
  exact Measure.map_infinitePi_infinitePi_of_inj injective

theorem innovationTreeShift_append (rule : Rule)
    (first second : List (Fin rule.edges))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    innovationTreeShift rule second (innovationTreeShift rule first marks) =
      innovationTreeShift rule (first ++ second) marks := by
  funext coordinate
  simp only [innovationTreeShift, List.append_assoc]

theorem innovationTreeShift_memLp (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (addressPrefix : List (Fin rule.edges)) {value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    {order : ℝ≥0∞} (integrable : MemLp value order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    MemLp (value ∘ innovationTreeShift rule addressPrefix) order
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  integrable.comp_measurePreserving (innovationTreeShift_preserving rule p positive belowOne fixedPoint addressPrefix)

noncomputable def innovationTreeShiftLp (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (addressPrefix : List (Fin rule.edges)) (order : ℝ≥0∞) :
    Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint) →+
      Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  Lp.compMeasurePreserving (innovationTreeShift rule addressPrefix)
    (innovationTreeShift_preserving rule p positive belowOne fixedPoint addressPrefix)

theorem innovationTreeShiftLp_norm (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (addressPrefix : List (Fin rule.edges)) (order : ℝ≥0∞)
    (value : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    ‖innovationTreeShiftLp rule p positive belowOne fixedPoint addressPrefix order value‖ = ‖value‖ :=
  Lp.norm_compMeasurePreserving value (innovationTreeShift_preserving rule p positive belowOne fixedPoint addressPrefix)

end IGSIII.Probability


