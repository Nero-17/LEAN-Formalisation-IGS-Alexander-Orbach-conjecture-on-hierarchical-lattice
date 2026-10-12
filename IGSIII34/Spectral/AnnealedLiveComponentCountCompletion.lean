import IGSIII34.Spectral.PositiveComponentCountCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace IGSIII34.Spectral
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped BigOperators Topology

local instance : MeasurableSpace OrientedState := ⊤
local instance : MeasurableSingletonClass OrientedState := ⟨fun _ => trivial⟩

theorem retainedComponentStateFrom_measurable_completion (rule : Rule)
    (ancestor : List (Fin rule.edges)) (address : List (Fin rule.edges × Bool))
    (parent : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → OrientedState)
    (parentMeasurable : Measurable parent) :
    Measurable (fun marks => retainedComponentStateFrom rule marks ancestor (parent marks) address) := by
  induction address generalizing ancestor parent with
  | nil => exact parentMeasurable
  | cons choice tail inductionHypothesis =>
      let child : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → OrientedState :=
        fun marks => componentChildState
          (rule.network.orientedChildState (parent marks).sourceSelected (parent marks).targetSelected
            (marks (ancestor, (parent marks).massOpened)) choice.1) choice.2
      have childMeasurable : Measurable child := by
        let response : OrientedState × (Configuration rule.edges × Configuration rule.edges) → OrientedState :=
          fun data => componentChildState
            (rule.network.orientedChildState data.1.sourceSelected data.1.targetSelected
              (if data.1.massOpened then data.2.1 else data.2.2) choice.1) choice.2
        have measurable := (measurable_of_countable response).comp
          (parentMeasurable.prodMk ((measurable_pi_apply (ancestor, true)).prodMk
            (measurable_pi_apply (ancestor, false))))
        convert measurable using 1
        funext marks
        dsimp only [child, response, Function.comp_def]
        cases (parent marks).massOpened <;> rfl
      exact inductionHypothesis (ancestor ++ [choice.1]) child childMeasurable

theorem actualLiveComponentCount_measurable_completion (rule : Rule) (depth : ℕ) :
    Measurable (fun marks => actualLiveComponentCountCompletion rule marks depth) := by
  classical
  unfold actualLiveComponentCountCompletion
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.measurable_sum
  intro word _
  have measurable := retainedComponentStateFrom_measurable_completion rule []
    (List.ofFn word) (fun _ => .connected) measurable_const
  have eventMeasurable : MeasurableSet {marks |
      retainedComponentState rule marks (List.ofFn word) ≠ .inactive} := by
    exact (measurableSet_eq_fun measurable measurable_const).compl
  exact Measurable.ite eventMeasurable measurable_const measurable_const

theorem actualLiveComponentCount_integrable_completion (rule : Rule) (depth : ℕ)
    (measure : Measure ((List (Fin rule.edges) × Bool) → Configuration rule.edges))
    [IsFiniteMeasure measure] :
    Integrable (fun marks => (actualLiveComponentCountCompletion rule marks depth : ℝ)) measure := by
  classical
  apply (integrable_const ((Fintype.card (Fin depth → (Fin rule.edges × Bool))) : ℝ)).mono'
    ((measurable_of_countable (fun count : ℕ => (count : ℝ))).comp
      (actualLiveComponentCount_measurable_completion rule depth)).aestronglyMeasurable
  apply Eventually.of_forall
  intro marks
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
  change (actualLiveComponentCountCompletion rule marks depth : ℝ) ≤ _
  have bound := Finset.card_le_card (Finset.filter_subset
    (fun word : Fin depth → (Fin rule.edges × Bool) =>
      retainedComponentState rule marks (List.ofFn word) ≠ .inactive) Finset.univ)
  simp only [Finset.card_univ] at bound
  exact_mod_cast bound

theorem actual_slot_population_expectation_Perron_bound_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ depth : ℕ,
      (∫ marks, markedComponentSlotResponseCompletion rule marks depth [] .connected
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤
          bound * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^depth := by
  obtain ⟨bound, boundPositive, moments⟩ := classicalRule.population_moment_bound p positive belowOne fixedPoint
    componentSlotLiveValuesCompletion
    (fun state => by cases state <;> norm_num [componentSlotLiveValuesCompletion]) 1
  refine ⟨bound, boundPositive, ?_⟩
  intro depth
  have transport := integral_map_of_stronglyMeasurable
    (μ := independentInnovationLaw rule p positive belowOne fixedPoint)
    (markedHistoryPath_measurable rule [] true)
    (((measurable_of_countable (fun history : rule.ConfigurationHistory depth =>
      Rule.ConfigurationHistory.weightedPopulation rule .connected
        componentSlotLiveValuesCompletion depth history)).comp (measurable_pi_apply depth)).stronglyMeasurable)
  rw [independentInnovationLaw_history_path] at transport
  dsimp only [Function.comp_def] at transport
  have equality : (∫ marks, markedComponentSlotResponseCompletion rule marks depth [] .connected
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) =
      ∫ path, Rule.ConfigurationHistory.weightedPopulation rule .connected
        componentSlotLiveValuesCompletion depth (path depth)
        ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint true := by
    rw [transport]
    apply integral_congr_ae
    filter_upwards [independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks crossing
    change componentSlotResponseCompletion (rule.generation depth).network
      (markedGenerationConfiguration rule marks depth [] true) .connected = _
    rw [componentSlotResponse_connected_eq_live_completion _ _
      (markedGenerationConfiguration_crosses rule marks crossing depth [] true)]
    simp only [Rule.ConfigurationHistory.weightedPopulation, markedHistoryPath,
      Rule.ConfigurationHistory.latest_ofFine]
  rw [equality]
  simpa only [pow_one, Nat.one_mul, show (LiveState.connected == LiveState.connected) = true from rfl]
    using moments depth .connected

theorem actual_live_component_count_expectation_Perron_bound_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ depth : ℕ,
      (∫ marks, (actualLiveComponentCountCompletion rule marks depth : ℝ)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤
          bound * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^depth := by
  obtain ⟨bound, boundPositive, moments⟩ := actual_slot_population_expectation_Perron_bound_completion
    rule classicalRule p positive belowOne fixedPoint
  refine ⟨bound, boundPositive, ?_⟩
  intro depth
  have responseIntegrable : Integrable
      (fun marks => markedComponentSlotResponseCompletion rule marks depth [] .connected)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    have integrable : Integrable (fun configuration : Configuration (rule.generation depth).edges =>
        componentSlotResponseCompletion (rule.generation depth).network configuration .connected)
        ((independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks => markedGenerationConfiguration rule marks depth [] true)) := Integrable.of_finite
    exact (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
      (markedGenerationConfiguration_measurable rule depth [] true).aemeasurable).mp integrable
  have comparison : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      (actualLiveComponentCountCompletion rule marks depth : ℝ) ≤
        markedComponentSlotResponseCompletion rule marks depth [] .connected := by
    filter_upwards [independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with marks crossing
    exact actualLiveComponentCount_le_slot_population_completion rule classicalRule marks crossing depth
  exact (integral_mono_ae (actualLiveComponentCount_integrable_completion rule depth _)
    responseIntegrable comparison).trans (moments depth)

end
end IGSIII34.Spectral
