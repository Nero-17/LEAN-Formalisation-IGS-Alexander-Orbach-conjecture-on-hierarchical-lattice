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

/-- The actual mass boundary is realized on the same actual compact chemical
limit as the full clusters, using only the classical rule and critical p. -/
theorem exists_actual_critical_component_boundary
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
          Tendsto (fun depth => ghDist
            (ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) growth growthPositive depth)
            (ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
              coherent growth growthPositive (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
              lengthNonnegative lengthPositive childConvergence)) atTop (𝓝 0) := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds, value, _, valuePositive, valueMean,
    amplitude, amplitudeAtLeastOne, fieldLimits, _, _, _, _⟩ :=
    exists_actual_chemical_scalar rule classicalRule p positive belowOne fixedPoint
  obtain ⟨weight, massProperties⟩ := actual_component_boundary_probability_law classicalRule p positive belowOne fixedPoint
  have growthGreaterThanOne : 1 < growth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le growthLower
  have growthPositive : 0 < growth := zero_lt_one.trans growthGreaterThanOne
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
  filter_upwards [fieldLimits, massProperties, independentInnovationLaw_crosses rule p positive belowOne fixedPoint,
    marked_generations_coherent_ae rule p positive belowOne fixedPoint,
    actual_critical_component_mesh_of_mean_bounds rule classicalRule p positive belowOne fixedPoint constant growth growthPositive
      meanBounds eta etaPositive etaBelowOne productGreaterThanOne]
    with marks fields masses crossing coherent mesh
  obtain ⟨lengthNonnegative, lengthPositive, childConvergence⟩ := actual_block_lengths_of_terminal_field
    rule p positive belowOne fixedPoint growth amplitude growthPositive (zero_lt_one.trans_le amplitudeAtLeastOne)
    value marks crossing (fun address => (fields address).1) (fun address => (fields address).2.2)
  obtain ⟨start, radiusBounds⟩ := mesh
  have rootCoherent := coherent [] true
  have compactness := actualChemicalSpace_compact_of_component_radius_bounds rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) rootCoherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    lengthNonnegative lengthPositive childConvergence marks (fun _ => rfl) eta ((rule.edges + 1 : ℝ) / (1 - eta)) start
    etaPositive.le etaBelowOne coefficientNonnegative radiusBounds
  letI := compactness
  obtain ⟨boundary, probability, atoms, retained⟩ := masses.2.2
  letI := probability
  have microscopicMesh : ∀ coarse fine (edge : Fin (rule.generation coarse).edges) side
      (vertex : Fin (rule.generation fine).vertices), start ≤ coarse →
      ((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).Reachable
          (plantedVertex (rule.generation fine).network side) vertex →
      (((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).dist
          ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
          ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) : ℝ) /
          growth ^ (coarse + fine + 2) ≤ ((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ (coarse + 1) := by
    intro coarse fine edge side vertex beyond reachable
    have distanceBound := generationBlockCellEmbedding_distance_to_planted_le rule coarse fine edge
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) side vertex reachable
    have normalized := div_le_div_of_nonneg_right (show
        (((rule.generation (coarse + fine + 1)).network.openGraph
          (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true)).dist
            ((generationBlockCellEmbedding rule coarse fine edge).vertex (plantedVertex (rule.generation fine).network side))
            ((generationBlockCellEmbedding rule coarse fine edge).vertex vertex) : ℝ) ≤
          (terminalComponentRadius (rule.generation fine).network (generationBlockCells rule coarse fine
            (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge) : ℝ) by exact_mod_cast distanceBound)
      (pow_pos growthPositive (coarse + fine + 2)).le
    have cellRadius := radiusBounds (generationEdgeAddress rule coarse edge)
      (markedGenerationConfiguration rule marks coarse [] true edge) fine (by
        rw [generationEdgeAddress_length]; omega)
    rw [generationEdgeAddress_length] at cellRadius
    rw [generationBlockCells_marked, List.nil_append] at normalized
    exact normalized.trans (by
      simpa only [markedTerminalComponentRadius, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using cellRadius)
  obtain ⟨realization, realizationMeasurable, pushProbability, realizationLimits, realizationTail, projectionLimits⟩ :=
    exists_actual_component_boundary_pushforward rule classicalRule marks crossing rootCoherent growth growthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive childConvergence boundary (by
        filter_upwards [retained] with path retained
        exact fun depth => ⟨(retained depth).1, (retained depth).2.2.1⟩)
      eta ((rule.edges + 1 : ℝ) / (1 - eta)) etaPositive.le etaBelowOne coefficientNonnegative start microscopicMesh
  have countLimits : ∀ address, Tendsto (fun fine => markedComponentVertexMass rule marks fine address /
      markedComponentVertexMass rule marks (fine + address.length) []) atTop (𝓝 (weight address marks)) :=
    fun address => (masses.2.1 address).2.2.1
  have levelSum := compatible_tree_weights_sum_one (fun address => weight address marks) masses.1
    (fun address => (masses.2.1 address).2.1)
  have meshVanishing : Tendsto (fun depth : ℕ => ((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ (depth + 1)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, mul_zero] using tendsto_const_nhds.mul
      ((tendsto_pow_atTop_nhds_zero_of_lt_one etaPositive.le etaBelowOne).comp (tendsto_add_atTop_nat 1))
  have denseAnchors := actual_connected_cylinder_anchors_dense rule classicalRule marks crossing rootCoherent growth growthPositive
    (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
    lengthNonnegative lengthPositive childConvergence
    (fun depth => ((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ (depth + 1))
    (fun depth => mul_nonneg coefficientNonnegative (pow_nonneg etaPositive.le _)) meshVanishing start microscopicMesh
  have fullSupport := boundary_pushforward_full_support boundary
    (fun _ word => weight (List.ofFn word) marks) atoms (fun depth => depth + start + 1)
    (fun depth word => actualComponentWordPoint rule classicalRule marks crossing rootCoherent growth growthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive childConvergence (depth + start) word)
    realization realizationMeasurable
    (fun depth => ((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ (start + 1) * eta ^ depth / (1 - eta))
    (by simpa only [mul_zero, zero_div] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one etaPositive.le etaBelowOne)).div_const (1 - eta))
    realizationTail (by
      intro point radius radiusPositive minimum
      obtain ⟨depth, beyond, word, stateConnected, close⟩ := denseAnchors point radius radiusPositive (minimum + start)
      have beyondStart : start ≤ depth := by omega
      refine ⟨depth - start, by omega, ?_⟩
      rw [Nat.sub_add_cancel beyondStart]
      exact ⟨word, (masses.2.1 (List.ofFn word)).2.2.2.2 stateConnected, close⟩)
  refine ⟨crossing, rootCoherent, lengthNonnegative, lengthPositive, childConvergence, compactness,
    (fun address => weight address marks), boundary, realization, masses.1,
    (fun address => ⟨(masses.2.1 address).1, countLimits address, (masses.2.1 address).2.2.2.2⟩),
    probability, atoms, realizationMeasurable, pushProbability, fullSupport.1, fullSupport.2,
    realizationLimits, projectionLimits, ?_, ?_⟩
  · intro age fallback
    exact component_empirical_projection_tendsto_zero rule marks crossing (fun address => weight address marks)
      (fun address => (masses.2.1 address).1) masses.1 countLimits levelSum boundary atoms (age + 1) fallback _
  · exact actualFiniteCluster_ghDist_tendsto_zero_of_component_radius_bounds rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) rootCoherent growth growthPositive
      (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive childConvergence marks (fun _ => rfl) eta ((rule.edges + 1 : ℝ) / (1 - eta)) start
      etaPositive.le etaBelowOne coefficientNonnegative radiusBounds

end
end IGSIII.Geometry
