import IGSIII.Chemical.SmallBall.ActualChemicalTerminalField
import IGSIII.Chemical.SmallBall.MarkedAnchorRetraction

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.SmallBall
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory Filter GromovHausdorff
open scoped Topology ENNReal

/-- Actual critical clusters converge to their chemical completion with the same two terminal marks. The limiting terminal distance is the positive root-field limit. -/
theorem exists_actual_critical_chemical_marked_gh
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
          ∃ crossing : ∀ depth, (rule.generation depth).network.crosses (markedGenerationConfiguration rule marks depth [] true) = true,
          ∃ compactness : CompactSpace (ActualChemicalSpace rule classicalRule
            (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
            (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
            lengthNonnegative lengthPositive childConvergence),
          letI := compactness
          Tendsto (fun depth => ghDist
            (ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) growth growthPositive depth)
            (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
              coherent growth growthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence)) atTop (𝓝 0) ∧
          dist (actualChemicalTerminal rule classicalRule
              (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent crossing growth growthPositive
              (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence true)
            (actualChemicalTerminal rule classicalRule
              (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent crossing growth growthPositive
              (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence false) =
            amplitude * chemicalField rule p positive belowOne fixedPoint value [] marks ∧
          0 < dist (actualChemicalTerminal rule classicalRule
              (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent crossing growth growthPositive
              (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence true)
            (actualChemicalTerminal rule classicalRule
              (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent crossing growth growthPositive
              (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence false) := by
  obtain ⟨constant, growth, _, _, growthLower, growthUpper, meanBounds, value, _, valuePositive, valueMean,
    amplitude, amplitudeAtLeastOne, fieldLimits, _, _, _, _⟩ :=
    exists_actual_chemical_scalar rule classicalRule p positive belowOne fixedPoint
  have growthGreaterThanOne : 1 < growth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le growthLower
  have growthPositive : 0 < growth := lt_trans zero_lt_one growthGreaterThanOne
  let eta : ℝ := (growth + 1) / (2 * growth)
  have etaPositive : 0 < eta := div_pos (by linarith) (by positivity)
  have etaBelowOne : eta < 1 := (div_lt_one (by positivity : 0 < 2 * growth)).mpr (by linarith)
  have productGreaterThanOne : 1 < growth * eta := by
    have identity : growth * eta = (growth + 1) / 2 := by dsimp [eta]; field_simp
    rw [identity]
    linarith
  have coefficientNonnegative : 0 ≤ (rule.edges + 1 : ℝ) / (1 - eta) :=
    div_nonneg (by positivity) (sub_pos.mpr etaBelowOne).le
  refine ⟨growth, growthPositive, growthLower, growthUpper, amplitude, amplitudeAtLeastOne, value, valuePositive, valueMean, ?_⟩
  filter_upwards [fieldLimits, independentInnovationLaw_crosses rule p positive belowOne fixedPoint,
    marked_generations_coherent_ae rule p positive belowOne fixedPoint,
    actual_critical_component_mesh_of_mean_bounds rule classicalRule p positive belowOne fixedPoint constant growth growthPositive
      meanBounds eta etaPositive etaBelowOne productGreaterThanOne] with marks fields crossing coherent mesh
  obtain ⟨lengthNonnegative, lengthPositive, childConvergence⟩ := actual_block_lengths_of_terminal_field
    rule p positive belowOne fixedPoint growth amplitude growthPositive (lt_of_lt_of_le zero_lt_one amplitudeAtLeastOne)
    value marks crossing (fun address => (fields address).1) (fun address => (fields address).2.2)
  obtain ⟨start, radiusBounds⟩ := mesh
  have rootCoherent := coherent [] true
  have compactness := actualChemicalSpace_compact_of_component_radius_bounds rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) rootCoherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    lengthNonnegative lengthPositive childConvergence marks (fun _ => rfl) eta ((rule.edges + 1 : ℝ) / (1 - eta)) start
    etaPositive.le etaBelowOne coefficientNonnegative radiusBounds
  have generationCrossing : ∀ depth, (rule.generation depth).network.crosses
      (markedGenerationConfiguration rule marks depth [] true) = true :=
    fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true
  refine ⟨rootCoherent, lengthNonnegative, lengthPositive, childConvergence, generationCrossing, compactness, ?_, ?_, ?_⟩
  · exact actualFiniteCluster_ghDist_tendsto_zero_of_component_radius_bounds rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) rootCoherent growth growthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive childConvergence marks (fun _ => rfl) eta ((rule.edges + 1 : ℝ) / (1 - eta)) start
      etaPositive.le etaBelowOne coefficientNonnegative radiusBounds
  · exact actualChemicalTerminal_distance_eq_field rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) rootCoherent generationCrossing growth growthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive childConvergence p positive belowOne fixedPoint amplitude value marks (fun _ => rfl) (fields []).2.2
  · exact actualChemicalTerminal_distance_positive rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) rootCoherent generationCrossing growth growthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive childConvergence p positive belowOne fixedPoint amplitude
      (lt_of_lt_of_le zero_lt_one amplitudeAtLeastOne) value marks (fun _ => rfl) (fields []).1 (fields []).2.2

end
end IGSIII.Chemical.SmallBall
