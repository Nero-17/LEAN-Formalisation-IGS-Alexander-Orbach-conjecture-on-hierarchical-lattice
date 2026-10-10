import IGSIII34.Diffusion.ActualDegreeConvergence
import IGSIII34.Diffusion.MarkedMeasureTransfer
import IGSIII.Geometry.CriticalComponentGHP

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall IGSIII.Geometry
open MeasureTheory Filter
open scoped BigOperators Topology

/-- Both degree and uniform counting probabilities converge on the actual
entire critical clusters to the same full-support probability on the same
compact chemical completion. The ordered terminal marks also converge. -/
theorem exists_actual_critical_degree_and_counting_marked_ghp
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ growth : ℝ, ∃ growthPositive : 0 < growth,
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      ∃ amplitude : ℝ, 1 ≤ amplitude ∧
      ∃ value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
        (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) ∧
        (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
        ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
          ∃ crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened,
          ∃ coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true),
          ∃ lengthNonnegative : ∀ coarse edge, 0 ≤ chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks coarse edge,
          ∃ lengthPositive : ∀ coarse edge, markedGenerationConfiguration rule marks coarse [] true edge = true →
            0 < chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks coarse edge,
          ∃ childConvergence : ∀ coarse edge, Tendsto (fun fine =>
            (((rule.generation fine).network.openGraph
              (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
                (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
              growth ^ (coarse + fine + 2)) atTop
              (𝓝 (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks coarse edge)),
          ∃ compactness : CompactSpace (ActualChemicalSpace rule classicalRule
            (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
            (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
            lengthNonnegative lengthPositive childConvergence),
          letI := compactness
          ∃ limitMeasure : Measure (ActualChemicalSpace rule classicalRule
            (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
            (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
            lengthNonnegative lengthPositive childConvergence),
            IsProbabilityMeasure limitMeasure ∧ limitMeasure.IsOpenPosMeasure ∧ limitMeasure.support = Set.univ ∧
            MarkedGHPConverges
              (fun depth => ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) growth growthPositive depth)
              (actualFiniteClusterDegreeMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
                (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive)
              limitMeasure
              (actualFiniteClusterTerminal rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
                (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive)
              (actualChemicalTerminal rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
                coherent (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive
                (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
                lengthNonnegative lengthPositive childConvergence) ∧
            MarkedGHPConverges
              (fun depth => ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) growth growthPositive depth)
              (actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true) growth growthPositive)
              limitMeasure
              (actualFiniteClusterTerminal rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
                (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive)
              (actualChemicalTerminal rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
                coherent (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive
                (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
                lengthNonnegative lengthPositive childConvergence) := by
  obtain ⟨growth, growthPositive, growthLower, growthUpper, amplitude, amplitudeAtLeastOne, value,
    valuePositive, valueMean, meanData, _, spaceData⟩ :=
    exists_actual_critical_component_marked_ghp rule classicalRule p positive belowOne fixedPoint
  obtain ⟨constant, _, _, meanBounds⟩ := meanData
  have growthGreaterThanOne : 1 < growth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le growthLower
  let eta : ℝ := (growth + 1) / (2 * growth)
  have etaPositive : 0 < eta := div_pos (by linarith) (by positivity)
  have etaBelowOne : eta < 1 := (div_lt_one (by positivity : 0 < 2 * growth)).mpr (by linarith)
  have productGreaterThanOne : 1 < growth * eta := by
    have identity : growth * eta = (growth + 1) / 2 := by dsimp [eta]; field_simp
    rw [identity]
    linarith
  obtain ⟨jointWeight, jointLimits⟩ := actual_joint_edge_counting_word_limits classicalRule p positive belowOne fixedPoint
  refine ⟨growth, growthPositive, growthLower, growthUpper, amplitude, amplitudeAtLeastOne, value, valuePositive, valueMean, ?_⟩
  filter_upwards [spaceData, jointLimits,
    actual_component_root_mass_tendsto_atTop classicalRule p positive belowOne fixedPoint,
    actual_critical_component_mesh_of_mean_bounds rule classicalRule p positive belowOne fixedPoint constant growth growthPositive
      meanBounds eta etaPositive etaBelowOne productGreaterThanOne]
    with marks data jointLimits massGrowth mesh
  obtain ⟨crossing, coherent, lengthNonnegative, lengthPositive, childConvergence, compactness,
    weight, boundary, realization, _, _, _, _, _, pushProbability, openPositive, support,
    _, _, _, markedGHP, _⟩ := data
  letI := compactness
  obtain ⟨start, radiusBound⟩ := mesh
  have comparison := actual_degree_counting_tendsto_zero_of_component_radius_bounds rule marks crossing coherent growth growthPositive
    eta ((rule.edges + 1 : ℝ) / (1 - eta)) start etaPositive.le etaBelowOne
    (div_nonneg (by positivity) (sub_pos.mpr etaBelowOne).le) radiusBound massGrowth
    (fun address => jointWeight address marks) jointLimits.2.2.2
  refine ⟨crossing, coherent, lengthNonnegative, lengthPositive, childConvergence, compactness,
    boundary.map realization, pushProbability, openPositive, support, ?_, markedGHP⟩
  exact markedGHPConverges_of_measure_distance_tendsto_zero _ _ _ _ _ _ markedGHP comparison

end
end IGSIII34.Diffusion
