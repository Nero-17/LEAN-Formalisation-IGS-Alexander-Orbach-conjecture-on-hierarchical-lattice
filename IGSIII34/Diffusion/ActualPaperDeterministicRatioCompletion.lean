import IGSIII34.Diffusion.ActualPaperDeterministicClocksCompletion
import IGSIII34.Diffusion.ActualCountingClockDensityCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology NNReal

/-- The ratio between the paper's deterministic Perron clock and the
original degree clock (false) or original vertex clock (true). -/
def actualPaperDeterministicClockRatioCompletion
    (rule : Rule) (p growth : ℝ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
    (countingSpeed : Bool) (depth : ℕ) : ℝ≥0 :=
  Real.toNNReal
    ((((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * growth) ^ (depth+1)) /
      (if countingSpeed then
        (Fintype.card (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth) : ℝ) * growth ^ (depth+1)
       else
        2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks depth)) * growth ^ (depth+1)))

theorem actualPaperDeterministicClockRatio_positive_completion
    (rule : Rule) (p growth : ℝ) (growthPositive : 0 < growth)
    (radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address copy, rule.network.crosses (marks (address, copy)) = copy)
    (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)
    (countingSpeed : Bool) (depth : ℕ) :
    0 < actualPaperDeterministicClockRatioCompletion rule p growth marks chemicalScale chemicalScalePositive countingSpeed depth := by
  letI : Nonempty (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth) :=
    ⟨⟨(rule.generation depth).network.source, SimpleGraph.Reachable.refl _⟩⟩
  letI := clusterEdge_nonempty (rule.generation depth).network (stationaryConfiguration rule marks depth)
    (markedGenerationConfiguration_crosses rule marks crossing depth [] true)
  unfold actualPaperDeterministicClockRatioCompletion
  apply Real.toNNReal_pos.mpr
  apply div_pos (pow_pos (mul_pos radiusPositive growthPositive) _)
  cases countingSpeed <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> positivity

/-- Both original walks have positive, explicitly computed limiting clock
ratios; this is a consequence of their common Perron mass, not a hypothesis. -/
theorem ae_actual_paper_deterministic_NNReal_ratios_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthPositive : 0 < growth) :
    ∃ (edgeCoefficient vertexCoefficient : ℝ)
      (mass : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      0 < edgeCoefficient ∧ 0 < vertexCoefficient ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        0 < mass marks ∧
        ∀ (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale) (countingSpeed : Bool),
          (∀ depth, 0 < actualPaperDeterministicClockRatioCompletion rule p growth marks chemicalScale chemicalScalePositive countingSpeed depth) ∧
          0 < Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks))) ∧
          Tendsto (actualPaperDeterministicClockRatioCompletion rule p growth marks chemicalScale chemicalScalePositive countingSpeed)
            atTop (𝓝 (Real.toNNReal (1 / (if countingSpeed then vertexCoefficient * mass marks else 2 * (edgeCoefficient * mass marks))))) := by
  obtain ⟨edgeCoefficient, vertexCoefficient, mass, edgePositive, vertexPositive, limits⟩ :=
    ae_actual_paper_deterministic_clock_limits_completion rule classicalRule p positive belowOne fixedPoint growth growthPositive
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  refine ⟨edgeCoefficient, vertexCoefficient, mass, edgePositive, vertexPositive, ?_⟩
  filter_upwards [limits, independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks properties crossing
  refine ⟨properties.1, ?_⟩
  intro chemicalScale chemicalScalePositive countingSpeed
  refine ⟨actualPaperDeterministicClockRatio_positive_completion rule p growth growthPositive radiusPositive marks crossing chemicalScale chemicalScalePositive countingSpeed, ?_, ?_⟩
  · apply Real.toNNReal_pos.mpr
    apply div_pos zero_lt_one
    cases countingSpeed
    · exact mul_pos (by norm_num) (mul_pos edgePositive properties.1)
    · exact mul_pos vertexPositive properties.1
  · cases countingSpeed
    · convert (continuous_real_toNNReal.tendsto _).comp (properties.2 chemicalScale chemicalScalePositive).1 using 1
      · funext depth
        rfl
      · rfl
    · convert (continuous_real_toNNReal.tendsto _).comp (properties.2 chemicalScale chemicalScalePositive).2 using 1
      · funext depth
        rfl
      · rfl

end
end IGSIII34.Diffusion



