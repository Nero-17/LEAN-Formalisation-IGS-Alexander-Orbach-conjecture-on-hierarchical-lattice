import IGSIII.Mass.ActualPopulationNormalization20261012
import IGSIII34.Diffusion.ActualPaperDeterministicClocksCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII.Geometry IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped Topology

/-- Current manuscript clock coefficients, on the actual common innovation
sample: vertex-normalized `W_c` and connected Perron coordinate `v_c`.
The growth exponent belongs to the fixed rule before any family parameter
varies. All count and clock limits are derived from the graph constructor. -/
theorem ae_actual_normalized_vertex_mass_clocks20261012
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (resistance : ℝ) (resistancePositive : 0 < resistance) :
    ∃ (h v : LiveState → ℝ)
      (stateMass : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ)
      (mass : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      (∀ state, 0 < h state) ∧ (∀ state, 0 < v state) ∧
      rule.network.massMatrix p *ᵥ h =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • h ∧
      v ᵥ* rule.network.massMatrix p =
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • v ∧
      v ⬝ᵥ h = 1 ∧
      (∀ state, (∫ path, stateMass state path
        ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint (state == .connected)) = h state) ∧
      (∀ marks, mass marks = stateMass .connected (markedHistoryPath rule [] true marks)) ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        0 < mass marks ∧ ∀ (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale),
        Tendsto (fun depth =>
          (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * resistance) ^ (depth + 1)) /
            (2 * Fintype.card (ClusterEdge (rule.generation depth).network (stationaryConfiguration rule marks depth)) * resistance ^ (depth + 1)))
          atTop (𝓝 (1 / (2 * v .connected * mass marks))) ∧
        Tendsto (fun depth =>
          (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal * resistance) ^ (depth + 1)) /
            ((Fintype.card (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth) : ℝ) * resistance ^ (depth + 1)))
          atTop (𝓝 (1 / mass marks)) ∧
        Tendsto (fun depth => (Fintype.card (ActualFiniteCluster rule (stationaryConfiguration rule marks)
            chemicalScale chemicalScalePositive depth) : ℝ) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ (depth + 1))
          atTop (𝓝 (mass marks)) := by
  obtain ⟨h, v, coefficient, stateMass, oldMass, hPositive, vPositive, hEigenvector,
    vEigenvector, normalized, _, _, means, _, limits⟩ :=
    classicalRule.actual_expected_mass_population_normalization20261012 p positive belowOne fixedPoint
  let mass (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :=
    stateMass .connected (markedHistoryPath rule [] true marks)
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  rw [← independentInnovationLaw_history_path rule p positive belowOne fixedPoint [] true] at limits
  have actual := ae_of_ae_map (markedHistoryPath_measurable rule [] true).aemeasurable limits
  refine ⟨h, v, stateMass, mass, hPositive, vPositive, hEigenvector,
    vEigenvector, normalized, means, fun _ => rfl, ?_⟩
  filter_upwards [actual, independentInnovationLaw_crosses rule p positive belowOne fixedPoint]
    with marks properties crossing
  have edgeLimit : Tendsto (fun depth => ((rule.generation depth).network.liveCount .connected .connected
      (markedGenerationConfiguration rule marks depth [] true) : ℝ) /
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
      atTop (𝓝 (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) *
        (mass marks * v .connected))) := by
    have shifted := ((properties.2.2.1 .connected).comp (tendsto_add_atTop_nat 1)).const_mul
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    convert shifted using 1
    ext depth
    simp only [Function.comp_apply, Rule.ConfigurationHistory.rootLevelPopulation_succ,
      Rule.ConfigurationHistory.weightedPopulation, markedHistoryPath,
      Rule.ConfigurationHistory.latest_ofFine, FiniteNetwork.liveResponse_eq,
      mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, mul_zero, pow_succ]
    field_simp [radiusPositive.ne']
  have vertexLimit : Tendsto (fun depth => (markedComponentVertexMass rule marks depth [] + 2) /
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
      atTop (𝓝 (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) * mass marks)) := by
    have shifted := (properties.2.2.2.comp (tendsto_add_atTop_nat 1)).const_mul
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    convert shifted using 1
    ext depth
    simp only [Function.comp_apply, Rule.ConfigurationHistory.rootLevelVertexCount_succ,
      Rule.ConfigurationHistory.vertexMass, markedHistoryPath, Rule.ConfigurationHistory.latest_ofFine,
      markedComponentVertexMass, componentEdgeAddress, List.map_nil, retainedComponentState,
      retainedComponentStateFrom, markedOrientedVertexMass, internalStateMass, OrientedState.sourceSelected,
      OrientedState.targetSelected, OrientedState.massOpened, decide_true,
      show (LiveState.connected == LiveState.both) = false from rfl]
    rw [(rule.generation depth).network.internalSelectedMass_connected _
      (markedGenerationConfiguration_crosses rule marks crossing depth [] true), pow_succ]
    field_simp [radiusPositive.ne']
    <;> ring
  refine ⟨properties.1, ?_⟩
  intro chemicalScale chemicalScalePositive
  have vertexCard (depth : ℕ) :
      (Fintype.card (ActualFiniteCluster rule (stationaryConfiguration rule marks) chemicalScale chemicalScalePositive depth) : ℝ) =
        markedComponentVertexMass rule marks depth [] + 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact actualFiniteCluster_card rule marks crossing chemicalScale chemicalScalePositive depth
  refine ⟨?_, ?_, ?_⟩
  · simpa only [clusterEdge_card, stationaryConfiguration, mul_assoc, mul_left_comm, mul_comm] using
      paper_deterministic_clock_ratio_completion20261011
        (fun depth => ((rule.generation depth).network.liveCount .connected .connected
          (markedGenerationConfiguration rule marks depth [] true) : ℝ))
        _ resistance 2 (mass marks * v .connected) radiusPositive resistancePositive.ne'
        (by norm_num) (mul_pos properties.1 (vPositive .connected)) edgeLimit
  · simpa only [vertexCard, one_mul] using paper_deterministic_clock_ratio_completion20261011
      (fun depth => markedComponentVertexMass rule marks depth [] + 2)
      _ resistance 1 (mass marks) radiusPositive resistancePositive.ne'
      zero_lt_one properties.1 vertexLimit
  · have divided := vertexLimit.div_const
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    convert divided using 1
    · ext depth
      rw [vertexCard, pow_succ]
      ring
    · simp [radiusPositive.ne']

end
end IGSIII34.Diffusion
