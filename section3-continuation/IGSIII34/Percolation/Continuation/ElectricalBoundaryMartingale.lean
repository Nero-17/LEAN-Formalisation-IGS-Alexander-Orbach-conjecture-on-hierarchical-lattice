import IGSIII34.Percolation.Continuation.ElectricalBoundaryTower
import IGSIII34.Probability.PrefixMartingale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory ProbabilityTheory Universality Universality.FiniteNetwork Filter
open IGSIII.Probability IGSIII.Chemical.Substitution IGSIII34.Probability
open scoped NNReal ENNReal _root_.Topology

def electricalBoundaryMarksPrefixFiltration (rule : Rule) : Filtration ℕ
    (inferInstance : MeasurableSpace ((List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0)) where
  seq depth := (coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length)
    (depth+1)).comap (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      fun coordinate => (sample coordinate).1)
  mono' := fun _ _ inequality => MeasurableSpace.comap_mono
    ((coordinatePrefixFiltration _).mono (Nat.add_le_add_right inequality 1))
  le' depth := (MeasurableSpace.comap_mono ((coordinatePrefixFiltration _).le (depth+1))).trans
    (show Measurable (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
      fun coordinate => (sample coordinate).1) from by fun_prop).comap_le

theorem electricalBoundaryMarksPrefixFiltration_eq_comap (rule : Rule) (depth : ℕ) :
    electricalBoundaryMarksPrefixFiltration rule depth =
      (inferInstance : MeasurableSpace
        ({coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1} → Configuration rule.edges)).comap
        (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
          fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1} =>
            (sample coordinate.val).1) := by
  change (coordinatePrefixFiltration _ (depth+1)).comap _ = _
  rw [coordinatePrefixFiltration_eq_comap, MeasurableSpace.comap_comp]
  rfl

def electricalBoundaryMeanProcess (rule : Rule) (law : ProbabilityMeasure ℝ≥0) (growth : ℝ≥0)
    (depth : ℕ) (sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0) : ℝ :=
  electricalBoundaryGenerationMean rule law depth (fun coordinate => (sample coordinate).1) / (growth:ℝ)^(depth+1)

theorem electricalBoundaryMeanProcess_stronglyAdapted (rule : Rule) (law : ProbabilityMeasure ℝ≥0)
    (growth : ℝ≥0) :
    StronglyAdapted (electricalBoundaryMarksPrefixFiltration rule) (electricalBoundaryMeanProcess rule law growth) := by
  intro depth
  rw [electricalBoundaryMarksPrefixFiltration_eq_comap]
  have factor : electricalBoundaryMeanProcess rule law growth depth =
      (fun history : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1} → Configuration rule.edges =>
        electricalBoundaryGenerationMean rule law depth (innovationPrefixFill rule (depth+1) history) /
          (growth:ℝ)^(depth+1)) ∘
      (fun sample : (List (Fin rule.edges) × Bool) → Configuration rule.edges × ℝ≥0 =>
        fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < depth+1} =>
          (sample coordinate.val).1) := by
    funext sample
    unfold electricalBoundaryMeanProcess electricalBoundaryGenerationMean
    dsimp only [Function.comp_def]
    rw [markedGenerationConfiguration_prefix_factor rule (fun coordinate => (sample coordinate).1) depth true]
  rw [factor]
  exact (((electricalBoundaryGenerationMean_measurable rule law depth).comp
    (innovationPrefixFill_measurable rule (depth+1))).div_const _).comp
      (comap_measurable _) |>.stronglyMeasurable

theorem electricalBoundaryTreeIteration_normalized_condExp_marks_prefix (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0))
    (growth : ℝ≥0) (growthPositive : 0 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    (first second : ℕ) (comparison : first ≤ second) :
    (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)[
      fun sample => (electricalBoundaryTreeIteration rule (second+1) sample:ℝ)/(growth:ℝ)^(second+1) |
        electricalBoundaryMarksPrefixFiltration rule first] =ᵐ[
          electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law]
        electricalBoundaryMeanProcess rule law growth first := by
  have depthEquality : (first+1)+(second-first) = second+1 := by omega
  have raw := electricalBoundaryTreeIteration_add_condExp_marks_prefix rule p positive belowOne fixedPoint
    law lawPositive secondMoment growth eigenlaw first (second-first)
  rw [depthEquality, ← electricalBoundaryMarksPrefixFiltration_eq_comap] at raw
  have scaling := condExp_smul (μ := electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law)
    ((growth:ℝ)^(second+1))⁻¹ (fun sample => (electricalBoundaryTreeIteration rule (second+1) sample:ℝ))
    (electricalBoundaryMarksPrefixFiltration rule first)
  have inputEquality : (fun sample => (electricalBoundaryTreeIteration rule (second+1) sample:ℝ)/(growth:ℝ)^(second+1)) =
      ((growth:ℝ)^(second+1))⁻¹ • (fun sample => (electricalBoundaryTreeIteration rule (second+1) sample:ℝ)) := by
    funext sample
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [inputEquality]
  refine scaling.trans ?_
  filter_upwards [raw] with sample raw
  change ((growth:ℝ)^(second+1))⁻¹ * _ = _
  rw [raw]
  unfold electricalBoundaryMeanProcess
  have growthRealNonzero : (growth:ℝ) ≠ 0 := by exact_mod_cast growthPositive.ne'
  have powerEquality : (growth:ℝ)^(second+1) =
      (growth:ℝ)^(first+1)*(growth:ℝ)^(second-first) := by rw [← pow_add, depthEquality]
  rw [powerEquality]
  field_simp [growthRealNonzero]

theorem electricalBoundaryMeanProcess_martingale (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0))
    (growth : ℝ≥0) (growthPositive : 0 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law) :
    Martingale (electricalBoundaryMeanProcess rule law growth) (electricalBoundaryMarksPrefixFiltration rule)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) := by
  refine ⟨electricalBoundaryMeanProcess_stronglyAdapted rule law growth, ?_⟩
  intro first second comparison
  have atSecond := electricalBoundaryTreeIteration_normalized_condExp_marks_prefix rule p positive belowOne fixedPoint
    law lawPositive secondMoment growth growthPositive eigenlaw second second le_rfl
  have atFirst := electricalBoundaryTreeIteration_normalized_condExp_marks_prefix rule p positive belowOne fixedPoint
    law lawPositive secondMoment growth growthPositive eigenlaw first second comparison
  exact (condExp_congr_ae atSecond).symm.trans
    ((condExp_condExp_of_le ((electricalBoundaryMarksPrefixFiltration rule).mono comparison)
      ((electricalBoundaryMarksPrefixFiltration rule).le second)).trans atFirst)

theorem electricalBoundaryMeanProcess_eLpNorm_two_bound (rule : Rule) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (law : ProbabilityMeasure ℝ≥0) (lawPositive : ∀ᵐ value ∂(law:Measure ℝ≥0), 0 < value)
    (secondMoment : Integrable (fun value : ℝ≥0 => (value:ℝ)^2) (law:Measure ℝ≥0))
    (growth : ℝ≥0) (growthPositive : 0 < growth)
    (eigenlaw : electricalOutputLaw rule p positive belowOne fixedPoint law = scaledProbabilityLaw growth law)
    (depth : ℕ) :
    eLpNorm (electricalBoundaryMeanProcess rule law growth depth) 2
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) ≤
      eLpNorm (fun value : ℝ≥0 => (value:ℝ)) 2 (law:Measure ℝ≥0) := by
  have conditional := electricalBoundaryTreeIteration_normalized_condExp_marks_prefix rule p positive belowOne fixedPoint
    law lawPositive secondMoment growth growthPositive eigenlaw depth depth le_rfl
  rw [← eLpNorm_congr_ae conditional]
  refine (eLpNorm_condExp_le_eLpNorm _ (by norm_num : (1:ℝ≥0∞) ≤ 2)).trans_eq ?_
  have preserving : MeasurePreserving (fun sample => (growth^(depth+1))⁻¹*electricalBoundaryTreeIteration rule (depth+1) sample)
      (electricalBoundaryInnovationLaw rule p positive belowOne fixedPoint law) (law:Measure ℝ≥0) :=
    ⟨measurable_const.mul (electricalBoundaryTreeIteration_measurable rule (depth+1)),
      electricalBoundaryTreeIteration_normalized_eigenlaw rule p positive belowOne fixedPoint law growth growthPositive eigenlaw (depth+1)⟩
  have transported := eLpNorm_comp_measurePreserving NNReal.continuous_coe.measurable.aestronglyMeasurable preserving (p := 2)
  simpa only [Function.comp_def, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow, div_eq_mul_inv, mul_comm] using transported

end
end IGSIII34.Percolation
