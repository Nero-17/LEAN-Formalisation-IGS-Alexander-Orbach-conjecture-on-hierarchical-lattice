import IGSIII.Geometry.CriticalComponentBoundary
import IGSIII.Geometry.ActualClusterMeasuredConvergence
import IGSIII.Mass.ComponentMassGrowth
import IGSIII.Geometry.ActualComponentBoundary
import IGSIII.Geometry.ComponentMassApproximation
import IGSIII.Geometry.CriticalChemicalLengths
import IGSIII.Geometry.ActualClusterGromovHausdorff
import IGSIII.Geometry.PositiveCylinderAnchors
import IGSIII.Geometry.BoundaryFullSupport

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall
open MeasureTheory Filter GromovHausdorff
open scoped BigOperators Topology

/-- The full retained finite clusters, with uniform vertex probability and
ordered terminal marks, converge in marked GHP to the full-support mass
boundary on the same compact chemical completion. Only the classical rule
and critical p are inputs. -/
theorem exists_actual_critical_component_marked_ghp
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
              lengthNonnegative lengthPositive childConvergence)) atTop (𝓝 0) := by
  obtain ⟨growth, growthPositive, growthLower, growthUpper, amplitude, amplitudeAtLeastOne, value,
    valuePositive, valueMean, meanData, fieldLimits, boundaryData⟩ :=
    exists_actual_critical_component_boundary rule classicalRule p positive belowOne fixedPoint
  obtain ⟨constant, constantPositive, constantAtMostOne, meanBounds⟩ := meanData
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
  have coefficientNonnegative : 0 ≤ (rule.edges + 1 : ℝ) / (1 - eta) :=
    div_nonneg (by positivity) (sub_pos.mpr etaBelowOne).le
  refine ⟨growth, growthPositive, growthLower, growthUpper, amplitude, amplitudeAtLeastOne, value,
    valuePositive, valueMean, ⟨constant, constantPositive, constantAtMostOne, meanBounds⟩, fieldLimits, ?_⟩
  filter_upwards [boundaryData, actual_component_root_mass_tendsto_atTop classicalRule p positive belowOne fixedPoint,
    actual_critical_component_mesh_of_mean_bounds rule classicalRule p positive belowOne fixedPoint constant growth growthPositive
      meanBounds eta etaPositive etaBelowOne productGreaterThanOne]
    with marks data massGrowth mesh
  obtain ⟨crossing, coherent, lengthNonnegative, lengthPositive, childConvergence, compactness,
    weight, boundary, realization, rootWeight, weights, probability, atoms, realizationMeasurable, pushProbability,
    openPositive, support, realizationLimits, projectionLimits, empiricalLimits, ghLimits⟩ := data
  letI := compactness
  letI := probability
  obtain ⟨start, radiusBound⟩ := mesh
  refine ⟨crossing, coherent, lengthNonnegative, lengthPositive, childConvergence, compactness,
    weight, boundary, realization, rootWeight, weights, probability, atoms, realizationMeasurable, pushProbability,
    openPositive, support, realizationLimits, projectionLimits, empiricalLimits, ?_, ghLimits⟩
  exact actualFiniteCluster_markedGHP_of_component_radius_bounds rule classicalRule marks crossing coherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    lengthNonnegative lengthPositive childConvergence eta ((rule.edges + 1 : ℝ) / (1 - eta)) start
    etaPositive.le etaBelowOne coefficientNonnegative radiusBound massGrowth weight
    (fun address => (weights address).1) (fun address => (weights address).2.1)
    boundary atoms realization projectionLimits

end
end IGSIII.Geometry
