import IGSIII.Geometry.CriticalComponentGHP
import IGSIII.Geometry.BoxDimensionSameWitness
import IGSIII.Geometry.FullComponentMesh
import IGSIII.Geometry.ChemicalMetricMeasureCode
import IGSIII.Geometry.ChemicalMeasureCodeFaithfulness
import IGSIII.Chemical.SmallBall.ActualChemicalMarkedGH
import IGSIII.Geometry.CellLocalisationCriticalMarkedLaw
import IGSIII.Geometry.CellLocalisationActualSimilarity
import IGSIII.Geometry.CellLocalisationActualSeparation
import IGSIII.Geometry.ChemicalDimensionComparison
import IGSIII.Chemical.SmallBall.DiamondScalar
import IGSIII.Chemical.SubstitutionPaths.FiveCycleGrowth
import IGSIII.Mass.FourStateMassPerron
import IGSIII.Mass.FourStateMassLimit

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall
open MeasureTheory Filter GromovHausdorff Matrix
open scoped BigOperators Topology ENNReal

/-- The actual full two-marked measured chemical limit, its full-support
measure, exact positive terminal distance, and both box dimensions on the same
space and same scalar witness. The actual all-depth diameter moments and
measurable labelled metric-measure representation use this identical scale. -/
theorem exists_actual_critical_section_two_geometry
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ growth : ℝ, ∃ growthPositive : 0 < growth,
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      ∃ amplitude : ℝ, 1 ≤ amplitude ∧
      ∃ value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks) ∧
      (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1 ∧
      (∃ constant : ℝ, 0 < constant ∧ constant ≤ 1 ∧ ∀ depth,
        growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
        manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) ∧
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address,
        0 < chemicalField rule p positive belowOne fixedPoint value address marks ∧
        ((edgePathFamily rule.network (marks (address, true))).shortest (fun edge =>
          chemicalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks)) =
          growth * chemicalField rule p positive belowOne fixedPoint value address marks ∧
        Tendsto (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
          atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks))) ∧
      (∀ order : ℝ≥0∞, order ≠ ∞ → ∀ address opened sourceSide,
        MemLp (markedComponentDiameterSupremum rule growth address opened sourceSide) order
          (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
      Measurable (chemicalMetricMeasureCode rule p positive belowOne fixedPoint growth amplitude value) ∧
      Measurable (chemicalMarkedMetricMeasureCode rule p positive belowOne fixedPoint growth amplitude value) ∧
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
        ∃ weight : List (Fin rule.edges × Bool) → ℝ,
        ∃ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
        ∃ realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
          ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
            coherent growth growthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
            lengthNonnegative lengthPositive childConvergence,
          weight [] = 1 ∧
          (∀ address, 0 ≤ weight address ∧
            Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
              markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 (weight address)) ∧
            (retainedComponentState rule marks address = .connected → 0 < weight address)) ∧
          IsProbabilityMeasure boundary ∧
          (∀ age word, boundary {path | path age = word} = ENNReal.ofReal (weight (List.ofFn word))) ∧
          Measurable realization ∧ IsProbabilityMeasure (boundary.map realization) ∧
          (boundary.map realization).IsOpenPosMeasure ∧ (boundary.map realization).support = Set.univ ∧
          (∀ᵐ path ∂boundary, Tendsto (fun depth => actualComponentWordPoint rule classicalRule marks
            crossing
            coherent growth growthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
            lengthNonnegative lengthPositive childConvergence depth (path (depth + 1))) atTop (𝓝 (realization path))) ∧
          Tendsto (fun depth => levyProkhorovEDist
            (boundary.map (fun path => actualComponentWordPoint rule classicalRule marks crossing coherent growth growthPositive
              (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence depth (path (depth + 1))))
            (boundary.map realization)) atTop (𝓝 0) ∧
          (∀ age (fallback : Fin (age + 1) → (Fin rule.edges × Bool)), Tendsto (fun fine => levyProkhorovEDist
            ((componentEmpiricalWordLaw rule marks crossing fine (age + 1) fallback).map
              (actualComponentWordPoint rule classicalRule marks crossing coherent growth growthPositive
                (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
                lengthNonnegative lengthPositive childConvergence age))
            (boundary.map (fun path => actualComponentWordPoint rule classicalRule marks crossing coherent growth growthPositive
              (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence age (path (age + 1))))) atTop (𝓝 0)) ∧
          MarkedGHPConverges
            (fun depth => ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) growth growthPositive depth)
            (actualFiniteClusterMeasure rule (fun depth => markedGenerationConfiguration rule marks depth [] true) growth growthPositive)
            (boundary.map realization)
            (actualFiniteClusterTerminal rule (fun depth => markedGenerationConfiguration rule marks depth [] true)
              (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive)
            (actualChemicalTerminal rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
              coherent (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive
              (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence) ∧
          Tendsto (fun depth => ghDist
            (ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) growth growthPositive depth)
            (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
              coherent growth growthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence)) atTop (𝓝 0) ∧
          lowerBoxDimension (ActualChemicalSpace rule classicalRule
            (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
            (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
            lengthNonnegative lengthPositive childConvergence) = ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth : ℝ) : EReal) ∧
          upperBoxDimension (ActualChemicalSpace rule classicalRule
            (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growthPositive
            (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
            lengthNonnegative lengthPositive childConvergence) = ((Real.log ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) / Real.log growth : ℝ) : EReal) ∧
          dist (actualChemicalTerminal rule classicalRule
              (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
              (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive
              (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence true) (actualChemicalTerminal rule classicalRule
              (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
              (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive
              (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence false) =
            amplitude * chemicalField rule p positive belowOne fixedPoint value [] marks ∧
          0 < dist (actualChemicalTerminal rule classicalRule
              (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
              (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive
              (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence true) (actualChemicalTerminal rule classicalRule
              (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
              (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive
              (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence false) ∧
          ∀ address, chemicalCylinderMassCode rule marks address = weight address := by
  obtain ⟨growth, growthPositive, growthLower, growthUpper, amplitude, amplitudeAtLeastOne, value,
    valuePositive, valueMean, meanData, fieldLimits, spaceData⟩ :=
    exists_actual_critical_component_marked_ghp rule classicalRule p positive belowOne fixedPoint
  obtain ⟨constant, constantPositive, constantAtMostOne, meanBounds⟩ := meanData
  have growthGreaterThanOne : 1 < growth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le growthLower
  have amplitudePositive : 0 < amplitude := zero_lt_one.trans_le amplitudeAtLeastOne
  have diameterMoments := (actual_critical_component_diameter_supremum_moments_of_mean_bounds
    rule classicalRule p positive belowOne fixedPoint constant growth growthPositive meanBounds).1
  have dimensions := actual_critical_box_dimension_of_mean_bounds_and_positive_field rule classicalRule
    p positive belowOne fixedPoint constant growth amplitude growthGreaterThanOne amplitudePositive meanBounds value valuePositive
  refine ⟨growth, growthPositive, growthLower, growthUpper, amplitude, amplitudeAtLeastOne, value,
    valuePositive, valueMean, ⟨constant, constantPositive, constantAtMostOne, meanBounds⟩, fieldLimits,
    diameterMoments, chemicalMetricMeasureCode_measurable rule p positive belowOne fixedPoint growth amplitude value,
    chemicalMarkedMetricMeasureCode_measurable rule p positive belowOne fixedPoint growth amplitude value, ?_⟩
  filter_upwards [spaceData, fieldLimits, dimensions] with marks data fields dimension
  obtain ⟨crossing, coherent, lengthNonnegative, lengthPositive, childConvergence, compactness,
    weight, boundary, realization, rootWeight, weights, probability, atoms, realizationMeasurable, pushProbability,
    openPositive, support, realizationLimits, projectionLimits, empiricalLimits, markedGHP, ghLimits⟩ := data
  letI := compactness
  have box := dimension coherent lengthNonnegative lengthPositive childConvergence
  refine ⟨crossing, coherent, lengthNonnegative, lengthPositive, childConvergence, compactness,
    weight, boundary, realization, rootWeight, weights, probability, atoms, realizationMeasurable, pushProbability,
    openPositive, support, realizationLimits, projectionLimits, empiricalLimits, markedGHP, ghLimits, box.1, box.2, ?_, ?_, ?_⟩
  · exact actualChemicalTerminal_distance_eq_field rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
      (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive childConvergence p positive belowOne fixedPoint amplitude value marks (fun _ => rfl) (fields []).2.2
  · exact actualChemicalTerminal_distance_positive rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
      (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true) growth growthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive childConvergence p positive belowOne fixedPoint amplitude amplitudePositive value marks
      (fun _ => rfl) (fields []).1 (fields []).2.2
  · exact fun address => chemicalCylinderMassCode_eq_limit rule marks address (weight address) (weights address).2.1

end
end IGSIII.Geometry
