import IGSIII34.Percolation.Continuation.ElectricalBoundaryMartingale
import Mathlib.MeasureTheory.Function.FactorsThrough

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal _root_.Topology

theorem electricalBoundaryMarksPrefixFiltration_generates_marks (rule : Rule) :
    (⨆ depth, electricalBoundaryMarksPrefixFiltration rule depth) =
      (inferInstance : MeasurableSpace ((List (Fin rule.edges) × Bool) → Configuration rule.edges)).comap
        (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
          fun coordinate => (sample coordinate).1) := by
  change (⨆ depth, (coordinatePrefixFiltration
    (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)).comap _) = _
  rw [← MeasurableSpace.comap_iSup]
  congr 1
  apply le_antisymm
  · exact iSup_le (fun depth => (coordinatePrefixFiltration _).le (depth+1))
  · calc
      _ = (⨆ depth, coordinatePrefixFiltration
          (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) depth) :=
        (coordinatePrefixFiltration_generates _).symm
      _ ≤ _ := by
        apply iSup_le
        intro depth
        exact le_iSup_of_le depth ((coordinatePrefixFiltration _).mono (Nat.le_add_right depth 1))

theorem electrical_eigenlaw_endogenous_boundary_limit_exists (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0))
    (growth : ℝ≥0) (growthPositive : 0 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law) :
    ∃ value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ,
      StronglyMeasurable value ∧
      MemLp value 2 (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
      (∀ᵐ sample ∂electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law,
        Tendsto (fun depth => electricalBoundaryMeanProcess rule law growth depth sample) atTop
          (𝓝 (value (fun coordinate => (sample coordinate).1)))) := by
  have martingale := electricalBoundaryMeanProcess_martingale rule p positive belowOne fixedPoint law lawPositive
    secondMoment growth growthPositive eigenlaw
  have lawMemLp := (memLp_two_iff_integrable_sq NNReal.continuous_coe.measurable.aestronglyMeasurable).mpr secondMoment
  have twoBound (depth : ℕ) : eLpNorm (electricalBoundaryMeanProcess rule law growth depth) 2
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) ≤
      (eLpNorm (fun value : ℝ≥0 => (value:ℝ)) 2 (law:Measure ℝ≥0)).toNNReal := by
    rw [ENNReal.coe_toNNReal lawMemLp.eLpNorm_ne_top]
    exact electricalBoundaryMeanProcess_eLpNorm_two_bound rule p positive belowOne fixedPoint law lawPositive
      secondMoment growth growthPositive eigenlaw depth
  have oneBound (depth : ℕ) : eLpNorm (electricalBoundaryMeanProcess rule law growth depth) 1
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) ≤
      (eLpNorm (fun value : ℝ≥0 => (value:ℝ)) 2 (law:Measure ℝ≥0)).toNNReal := by
    exact (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num : (1:ℝ≥0∞) ≤ 2)
      ((martingale.stronglyMeasurable depth).mono
        ((electricalBoundaryMarksPrefixFiltration rule).le depth)).aestronglyMeasurable).trans (twoBound depth)
  have limitConvergence := martingale.submartingale.ae_tendsto_limitProcess oneBound
  have limitMemLp := martingale.submartingale.memLp_limitProcess twoBound
  have limitMeasurable : StronglyMeasurable[
      (inferInstance : MeasurableSpace ((List (Fin rule.edges) × Bool) → Configuration rule.edges)).comap
        (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
          fun coordinate => (sample coordinate).1)]
      ((electricalBoundaryMarksPrefixFiltration rule).limitProcess (electricalBoundaryMeanProcess rule law growth)
        (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)) := by
    rw [← electricalBoundaryMarksPrefixFiltration_generates_marks]
    exact Filtration.stronglyMeasurable_limitProcess
  obtain ⟨value, valueMeasurable, equality⟩ := limitMeasurable.exists_eq_measurable_comp
  have marksMeasurable : Measurable (fun sample :
      (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
        fun coordinate => (sample coordinate).1) := by fun_prop
  have valueMemLp : MemLp value 2 (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    have transported := (memLp_map_measure_iff valueMeasurable.aestronglyMeasurable marksMeasurable.aemeasurable).mpr
      (equality ▸ limitMemLp)
    rwa [electricalBoundaryInnovationLaw_marks_map] at transported
  refine ⟨value, valueMeasurable, valueMemLp, ?_⟩
  rwa [equality] at limitConvergence

end
end IGSIII34.Percolation
