import IGSIII34.Diffusion.ActualElectricalComponentCompletion
import IGSIII34.ResistanceLimit.RadiusMoments
import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion
import IGSIII34.Diffusion.ActualNaturalComponentIntrinsicWitness
import IGSIII.Geometry.ChemicalMetricMeasureCode
import IGSIII34.ResistanceLimit.RadiusSupremumSubexponential

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2800000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped _root_.Topology ENNReal

local instance : MeasurableSpace OrientedState := ⊤
local instance : MeasurableSingletonClass OrientedState := ⟨fun _ => trivial⟩

/-- The manuscript's local intrinsic diameter envelope for an actual
selected word. Both sides use the full radius of its original coarse state. -/
def actualComponentIntrinsicDiameterEnvelope (rule : Rule) (growth : ℝ)
    (word : List (Fin rule.edges × Bool))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  2 * markedElectricalRadiusSupremum rule growth (componentEdgeAddress word)
    (retainedComponentState rule marks word).massOpened marks

/-- The microscopic block response at any actual address, in either state,
converges to its stationary intrinsic electrical weight. -/
theorem actual_component_block_resistance_limit (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (growth : ℝ) (field : List (Fin rule.edges) → ℝ)
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address)
      atTop (𝓝 (field address)))
    (address : List (Fin rule.edges)) (opened : Bool) (coarse : ℕ)
    (edge : {edge : Fin (rule.generation coarse).edges // markedGenerationConfiguration rule marks coarse address opened edge = true}) :
    Tendsto (fun fine => (growth ^ (coarse + fine + 2))⁻¹ *
      unitConfigurationResistance (rule.generation fine).network
        (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge.val))
      atTop (𝓝 (stationaryGenerationResistance rule field growth coarse address edge.val)) := by
  have shifted := ((fieldLimit (address ++ generationEdgeAddress rule coarse edge.val)).comp
    (tendsto_add_atTop_nat 1)).const_mul (growth⁻¹ ^ (coarse + 1))
  apply shifted.congr'
  apply Eventually.of_forall
  intro fine
  dsimp only [Function.comp_def]
  rw [generationBlockCells_marked, edge.property]
  rw [markedGeneration_resistance_eq_iteration rule marks crossing]
  simp only [inv_pow]
  rw [show coarse + fine + 2 = (coarse + 1) + (fine + 1) by omega]
  simp only [pow_add, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]

/-- This convergence takes place inside the selected local component. It
does not use an embedding into the global graph or a Rayleigh comparison. -/
theorem actual_component_skeleton_resistances_tendsto (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (growth : ℝ) (growthPositive : 0 < growth) (field : List (Fin rule.edges) → ℝ)
    (fieldNonnegative : ∀ address, 0 ≤ field address)
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address)
      atTop (𝓝 (field address)))
    (address : List (Fin rule.edges)) (opened : Bool) (coarse : ℕ)
    {first last : Fin (rule.generation coarse).vertices}
    (reachable : ((rule.generation coarse).network.openGraph
      (markedGenerationConfiguration rule marks coarse address opened)).Reachable first last) :
    Tendsto (fun fine => (growth ^ (coarse + fine + 2))⁻¹ *
      pairResistance (network (rule.generation (coarse + fine + 1)).network
        (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)) (fun _ => 1)
        (blockOldVertexEmbedding rule coarse fine first) (blockOldVertexEmbedding rule coarse fine last))
      atTop (𝓝 (pairResistance (network (rule.generation coarse).network
        (markedGenerationConfiguration rule marks coarse address opened))
        (fun edge => stationaryGenerationResistance rule field growth coarse address edge.val) first last)) := by
  exact actual_block_skeleton_resistances_tendsto rule
    (fun depth => markedGenerationConfiguration rule marks depth address opened)
    (fun depth => markedGenerationConfiguration_coarsens rule marks crossing depth address opened)
    growth growthPositive coarse
    (fun edge => stationaryGenerationResistance rule field growth coarse address edge.val)
    (fun edge => mul_nonneg (pow_nonneg (inv_nonneg.mpr growthPositive.le) _) (fieldNonnegative _))
    (actual_component_block_resistance_limit rule marks crossing growth field fieldLimit address opened coarse) reachable

theorem actual_component_stationary_pair_le_radius_envelope (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (growth : ℝ) (growthPositive : 0 < growth) (field : List (Fin rule.edges) → ℝ)
    (fieldNonnegative : ∀ address, 0 ≤ field address)
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks depth address)
      atTop (𝓝 (field address)))
    (address : List (Fin rule.edges)) (opened sourceSide : Bool)
    (envelope : ℝ)
    (radiusBounds : ∀ depth, markedElectricalRadius rule marks depth address opened / growth ^ (depth + 1) ≤ envelope)
    (coarse : ℕ)
    (first last : RetainedComponentVertex (rule.generation coarse).network
      (markedGenerationConfiguration rule marks coarse address opened) sourceSide) :
    pairResistance (network (rule.generation coarse).network
      (markedGenerationConfiguration rule marks coarse address opened))
      (fun edge => stationaryGenerationResistance rule field growth coarse address edge.val) first.val last.val ≤ 2 * envelope := by
  apply le_of_tendsto (actual_component_skeleton_resistances_tendsto rule marks crossing growth growthPositive
    field fieldNonnegative fieldLimit address opened coarse (first.property.symm.trans last.property))
  apply Eventually.of_forall
  intro fine
  have lifted (vertex : RetainedComponentVertex (rule.generation coarse).network
      (markedGenerationConfiguration rule marks coarse address opened) sourceSide) :
      ((rule.generation (coarse + fine + 1)).network.openGraph
        (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened)).Reachable
        (plantedVertex (rule.generation (coarse + fine + 1)).network sourceSide)
        (blockOldVertexEmbedding rule coarse fine vertex.val) := by
    rw [← blockOldVertexEmbedding_planted rule coarse fine sourceSide]
    apply (blockOldVertexEmbedding_reachable_iff rule coarse fine _ _ _).mpr
    rw [generationBlockCoarse_of_coherent rule
      (fun depth => markedGenerationConfiguration rule marks depth address opened)
      (fun depth => markedGenerationConfiguration_coarsens rule marks crossing depth address opened) coarse fine]
    exact vertex.property
  have finiteBound := component_pairResistance_le_twice_radius
    (network (rule.generation (coarse + fine + 1)).network
      (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened))
    (fun _ => 1) (fun _ => zero_lt_one) sourceSide
    (blockOldVertexEmbedding rule coarse fine first.val) (blockOldVertexEmbedding rule coarse fine last.val)
    (by rw [graph_eq_openGraph]; exact lifted first)
    (by rw [graph_eq_openGraph]; exact lifted last)
  have normalized := mul_le_mul_of_nonneg_left finiteBound
    (inv_nonneg.mpr (pow_pos growthPositive (coarse + fine + 2)).le)
  have radiusBound := radiusBounds (coarse + fine + 1)
  change markedElectricalRadius rule marks (coarse + fine + 1) address opened /
    growth ^ (coarse + fine + 1 + 1) ≤ envelope at radiusBound
  rw [div_eq_mul_inv] at radiusBound
  change (growth ^ (coarse + fine + 2))⁻¹ * _ ≤ _ at normalized
  change (growth ^ (coarse + fine + 2))⁻¹ * _ ≤ 2 * envelope
  have exponent : coarse + fine + 1 + 1 = coarse + fine + 2 := by omega
  rw [exponent] at radiusBound
  change _ ≤ (growth ^ (coarse + fine + 2))⁻¹ * (2 * markedElectricalRadius rule marks (coarse + fine + 1) address opened) at normalized
  nlinarith

/-- A uniform finite intrinsic distance bound survives the direct limit and
its metric completion. -/
theorem rootedElectricalSpace_distance_le_of_finite_pairs
    (rule : Rule) (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
    (resistance : ∀ depth, {edge : Fin (rule.generation depth).edges // configuration depth edge = true} → ℝ)
    (positive : ∀ depth edge, 0 < resistance depth edge)
    (compatible : ∀ depth (first last : Fin (rule.generation depth).vertices),
      ((rule.generation depth).network.openGraph (configuration depth)).Reachable first last →
      pairResistance (network (rule.generation (depth + 1)).network (configuration (depth + 1)))
        (resistance (depth + 1)) (rule.generationOldVertex depth first) (rule.generationOldVertex depth last) =
      pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first last)
    (bound : ℝ)
    (finitePairs : ∀ depth (first last : RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide),
      pairResistance (network (rule.generation depth).network (configuration depth)) (resistance depth) first.val last.val ≤ bound)
    (first last : RootedElectricalSpace rule configuration coherent sourceSide resistance positive compatible) :
    dist first last ≤ bound := by
  refine UniformSpace.Completion.induction_on₂ first last (isClosed_le continuous_dist continuous_const) ?_
  intro first last
  rw [UniformSpace.Completion.coe_isometry.dist_eq]
  refine DirectLimit.induction₂
    (Universality.Geometry.IsometricSequence.transition
      (fun depth => RetainedComponentVertex (rule.generation depth).network (configuration depth) sourceSide)
      (retainedComponentOldEmbedding rule configuration coherent sourceSide)) (fun depth first last => ?_) first last
  change dist (rootedElectricalSkeletonVertex rule configuration coherent sourceSide resistance positive compatible depth first)
    (rootedElectricalSkeletonVertex rule configuration coherent sourceSide resistance positive compatible depth last) ≤ bound
  rw [rootedElectricalSkeletonVertex_distance]
  exact finitePairs depth first last

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (word : List (Fin rule.edges × Bool))

/-- The literal intrinsic completed selected component has diameter at most
twice the supremum of its actual microscopic unit-edge radii, in local units. -/
theorem actualElectricalComponent_intrinsic_diameter_le_radius_envelope
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (radiusBounds : ∀ depth, markedElectricalRadius rule marks.val depth (componentEdgeAddress word)
      (retainedComponentState rule marks.val word).massOpened / growth ^ (depth + 1) ≤
      markedElectricalRadiusSupremum rule growth (componentEdgeAddress word)
        (retainedComponentState rule marks.val word).massOpened marks.val) :
    Metric.diam (Set.univ : Set (ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks word)) ≤
      2 * markedElectricalRadiusSupremum rule growth (componentEdgeAddress word)
        (retainedComponentState rule marks.val word).massOpened marks.val := by
  have radiusNonnegative : 0 ≤ markedElectricalRadiusSupremum rule growth (componentEdgeAddress word)
      (retainedComponentState rule marks.val word).massOpened marks.val :=
    (div_nonneg (terminalResistanceRadius_nonnegative _ _) (pow_pos growthPositive 1).le).trans (radiusBounds 0)
  apply Metric.diam_le_of_forall_dist_le (mul_nonneg zero_le_two radiusNonnegative)
  intro first _ last _
  exact rootedElectricalSpace_distance_le_of_finite_pairs rule
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word)
    (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks word)
    (retainedComponentState rule marks.val word).sourceSelected
    (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word)
    (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word)
    (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks word)
    (2 * markedElectricalRadiusSupremum rule growth (componentEdgeAddress word)
      (retainedComponentState rule marks.val word).massOpened marks.val)
    (actual_component_stationary_pair_le_radius_envelope rule marks.val marks.property.2.1 growth growthPositive
      (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val)
      (fun address => (marks.property.1 address).le) fieldLimit (componentEdgeAddress word)
      (retainedComponentState rule marks.val word).massOpened (retainedComponentState rule marks.val word).sourceSelected _ radiusBounds)
    first last

/-- The diameter bridge applies almost surely to the original natural
physical endpoint; its field convergence and radius bounds are proved inputs
from the model, rather than assumptions in the conclusion. -/
theorem natural_actualElectricalComponent_intrinsic_diameter_envelope
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint) :
    ∀ᵐ rawMarks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ (typical : ComponentElectricalTypical rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) rawMarks) (word : List (Fin rule.edges × Bool)),
      Metric.diam (Set.univ : Set (ActualElectricalComponentSpace rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨rawMarks, typical⟩ word)) ≤
        2 * markedElectricalRadiusSupremum rule natural.growth (componentEdgeAddress word)
          (retainedComponentState rule rawMarks word).massOpened rawMarks := by
  obtain ⟨constant, constantPositive, growthBounds, membership, fixed⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  filter_upwards [actual_electrical_field_limits_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant natural.growth constantPositive (zero_lt_one.trans natural.aboveOne) growthBounds
      (natural.amplitude • natural.field) fixed membership,
    (actual_markedElectricalRadiusSupremum_memLp_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant natural.growth constantPositive natural.aboveOne growthBounds (natural.amplitude • natural.field)
      fixed membership 1 (by simp)).2] with rawMarks fieldLimit radiusBounds
  intro typical word
  exact actualElectricalComponent_intrinsic_diameter_le_radius_envelope rule p positive belowOne fixedPoint
    natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨rawMarks, typical⟩ word
    fieldLimit (radiusBounds _ _)

/-- Every selected-word diameter envelope has every finite moment, including
when the original coarse state is selected from the same environment. -/
theorem natural_actualComponentIntrinsicDiameterEnvelope_memLp
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
    (word : List (Fin rule.edges × Bool)) (order : ℝ≥0∞) (orderFinite : order ≠ ∞) :
    MemLp (actualComponentIntrinsicDiameterEnvelope rule natural.growth word) order
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  classical
  obtain ⟨constant, constantPositive, growthBounds, membership, fixed⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  have moments := (actual_markedElectricalRadiusSupremum_memLp_fixed_cluster rule classicalRule p positive belowOne fixedPoint
    constant natural.growth constantPositive natural.aboveOne growthBounds (natural.amplitude • natural.field)
    fixed membership order orderFinite).1
  have stateMeasurable : Measurable (fun marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges =>
      (retainedComponentState rule marks word).massOpened) :=
    (measurable_of_countable (fun state : OrientedState => state.massOpened)).comp
      (retainedComponentStateFrom_measurable rule [] .connected word)
  have eventMeasurable : MeasurableSet {marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges |
      (retainedComponentState rule marks word).massOpened = true} :=
    measurableSet_eq_fun stateMeasurable measurable_const
  have selected := MemLp.piecewise eventMeasurable
    ((moments (componentEdgeAddress word) true).restrict _)
    ((moments (componentEdgeAddress word) false).restrict _)
  convert selected.const_mul (2 : ℝ) using 1
  funext marks
  cases state : (retainedComponentState rule marks word).massOpened <;>
    simp only [actualComponentIntrinsicDiameterEnvelope, Set.piecewise, Set.mem_setOf_eq,
      state, Bool.false_eq_true, ↓reduceIte]

theorem natural_actualComponentIntrinsicDiameterEnvelope_positive_moments
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
    (word : List (Fin rule.edges × Bool)) (exponent : ℝ) (exponentPositive : 0 < exponent) :
    Integrable (fun marks => actualComponentIntrinsicDiameterEnvelope rule natural.growth word marks ^ exponent)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  have normMoment := (natural_actualComponentIntrinsicDiameterEnvelope_memLp rule classicalRule p positive belowOne fixedPoint
    natural word (ENNReal.ofReal exponent) (by simp)).integrable_norm_rpow'
  rw [ENNReal.toReal_ofReal exponentPositive.le] at normMoment
  obtain ⟨constant, constantPositive, growthBounds, membership, fixed⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  apply normMoment.congr
  filter_upwards [(actual_markedElectricalRadiusSupremum_memLp_fixed_cluster rule classicalRule p positive belowOne fixedPoint
      constant natural.growth constantPositive natural.aboveOne growthBounds (natural.amplitude • natural.field)
      fixed membership 1 (by simp)).2] with marks radiusBounds
  have radiusNonnegative : 0 ≤ markedElectricalRadiusSupremum rule natural.growth (componentEdgeAddress word)
      (retainedComponentState rule marks word).massOpened marks :=
    (div_nonneg (terminalResistanceRadius_nonnegative _ _)
      (pow_pos (zero_lt_one.trans natural.aboveOne) 1).le).trans (radiusBounds _ _ 0)
  have envelopeNonnegative : 0 ≤ actualComponentIntrinsicDiameterEnvelope rule natural.growth word marks :=
    mul_nonneg zero_le_two radiusNonnegative
  rw [Real.norm_eq_abs, abs_of_nonneg envelopeNonnegative]

/-- A nonvacuous original-model entry point: the actual intrinsic component
carrier exists on one probability-one event, all words have the stated
diameter envelope, and these envelopes and diameters are subexponential
simultaneously for every slack greater than one. -/
theorem natural_actualElectricalComponent_intrinsic_diameter_subexponential
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint) :
    ∀ᵐ rawMarks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ typical : ComponentElectricalTypical rule p positive belowOne fixedPoint natural.growth
          (natural.amplitude • natural.field) rawMarks,
        (∀ word : List (Fin rule.edges × Bool),
          Metric.diam (Set.univ : Set (ActualElectricalComponentSpace rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨rawMarks, typical⟩ word)) ≤
            actualComponentIntrinsicDiameterEnvelope rule natural.growth word rawMarks) ∧
        ∀ slack : ℝ, 1 < slack → ∃ bound : ℝ, 0 < bound ∧
          ∀ word : List (Fin rule.edges × Bool),
            actualComponentIntrinsicDiameterEnvelope rule natural.growth word rawMarks ≤ bound * slack ^ word.length ∧
            Metric.diam (Set.univ : Set (ActualElectricalComponentSpace rule p positive belowOne fixedPoint natural.growth
              (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨rawMarks, typical⟩ word)) ≤
              bound * slack ^ word.length := by
  filter_upwards [natural_actualElectricalComponent_intrinsic_diameter_envelope rule classicalRule p positive belowOne fixedPoint natural,
    ae_actual_natural_component_electrical_typical rule p positive belowOne fixedPoint natural,
    ae_natural_markedElectricalRadiusSupremum_subexponential_completion rule classicalRule p positive belowOne fixedPoint natural]
      with rawMarks diameterBounds typical subexponential
  refine ⟨typical, (fun word => diameterBounds typical word), ?_⟩
  intro slack slackGreaterThanOne
  obtain ⟨bound, boundPositive, radiusBounds⟩ := subexponential slack slackGreaterThanOne
  refine ⟨2 * bound, mul_pos zero_lt_two boundPositive, ?_⟩
  intro word
  have envelopeBound : actualComponentIntrinsicDiameterEnvelope rule natural.growth word rawMarks ≤
      (2 * bound) * slack ^ word.length := by
    have boundAtWord := mul_le_mul_of_nonneg_left
      (radiusBounds (componentEdgeAddress word) (retainedComponentState rule rawMarks word).massOpened) zero_le_two
    simpa only [actualComponentIntrinsicDiameterEnvelope, componentEdgeAddress, List.length_map, mul_assoc] using boundAtWord
  exact ⟨envelopeBound, (diameterBounds typical word).trans envelopeBound⟩

/-- The original finite classical model constructs the natural field,
the actual intrinsic completed component carriers, all positive moments of
their diameter envelopes, and the simultaneous subexponential bounds. -/
theorem exists_actual_intrinsic_component_diameter_envelopes
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint,
      (∀ (word : List (Fin rule.edges × Bool)) (exponent : ℝ), 0 < exponent →
        Integrable (fun marks => actualComponentIntrinsicDiameterEnvelope rule natural.growth word marks ^ exponent)
          (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
      ∀ᵐ rawMarks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∃ typical : ComponentElectricalTypical rule p positive belowOne fixedPoint natural.growth
            (natural.amplitude • natural.field) rawMarks,
          (∀ word : List (Fin rule.edges × Bool),
            Metric.diam (Set.univ : Set (ActualElectricalComponentSpace rule p positive belowOne fixedPoint natural.growth
              (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨rawMarks, typical⟩ word)) ≤
              actualComponentIntrinsicDiameterEnvelope rule natural.growth word rawMarks) ∧
          ∀ slack : ℝ, 1 < slack → ∃ bound : ℝ, 0 < bound ∧
            ∀ word : List (Fin rule.edges × Bool),
              actualComponentIntrinsicDiameterEnvelope rule natural.growth word rawMarks ≤ bound * slack ^ word.length ∧
              Metric.diam (Set.univ : Set (ActualElectricalComponentSpace rule p positive belowOne fixedPoint natural.growth
                (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨rawMarks, typical⟩ word)) ≤
                bound * slack ^ word.length := by
  obtain ⟨natural⟩ := exists_natural_resistance_completion rule classicalRule p positive belowOne fixedPoint
  exact ⟨natural,
    natural_actualComponentIntrinsicDiameterEnvelope_positive_moments rule classicalRule p positive belowOne fixedPoint natural,
    natural_actualElectricalComponent_intrinsic_diameter_subexponential rule classicalRule p positive belowOne fixedPoint natural⟩

end
end IGSIII34.Diffusion
