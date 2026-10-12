import IGSIII34.Spectral.RetainedMassMeanBoundCompletion
import IGSIII34.Spectral.TerminalCollarCountingCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open IGSIII34.Percolation MeasureTheory ProbabilityTheory Filter Matrix IGSIII.Geometry
open scoped BigOperators

local instance : MeasurableSpace OrientedState := ⊤
local instance : MeasurableSingletonClass OrientedState := ⟨fun _ => trivial⟩

def actualLiveIndicatorCompletion (rule : Rule) (word : List (Fin rule.edges × Bool))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  if retainedComponentState rule marks word ≠ .inactive then 1 else 0

theorem actualLiveIndicator_measurable_completion (rule : Rule)
    (word : List (Fin rule.edges × Bool)) :
    Measurable (actualLiveIndicatorCompletion rule word) :=
  Measurable.ite
    (measurableSet_eq_fun (retainedComponentStateFrom_measurable_completion
      rule [] word (fun _ => .connected) measurable_const) measurable_const).compl
    measurable_const measurable_const

theorem actualLiveIndicator_integrable_completion (rule : Rule)
    (word : List (Fin rule.edges × Bool))
    (measure : Measure ((List (Fin rule.edges) × Bool) → Configuration rule.edges))
    [IsFiniteMeasure measure] :
    Integrable (actualLiveIndicatorCompletion rule word) measure := by
  apply (integrable_const (1 : ℝ)).mono'
    (actualLiveIndicator_measurable_completion rule word).aestronglyMeasurable
  exact Eventually.of_forall (fun marks => by
    dsimp only [actualLiveIndicatorCompletion]; split_ifs <;> norm_num)

theorem actual_coarse_live_descendant_mass_product_completion
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion rule p positive belowOne fixedPoint)
    (word : List (Fin rule.edges × Bool)) (suffix : List (Fin rule.edges)) (parent : OrientedState) :
    Integrable (fun marks => actualLiveIndicatorCompletion rule word marks *
      continuation.mass parent (innovationTreeShift rule (componentEdgeAddress word ++ suffix) marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
    (∫ marks, actualLiveIndicatorCompletion rule word marks *
      continuation.mass parent (innovationTreeShift rule (componentEdgeAddress word ++ suffix) marks)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) =
      (∫ marks, actualLiveIndicatorCompletion rule word marks
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) *
      (∫ marks, continuation.mass parent marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) := by
  classical
  let address := componentEdgeAddress word ++ suffix
  have longer : word.length ≤ address.length := by
    simp only [address, componentEdgeAddress, List.length_append, List.length_map]
    omega
  let historyIndicator := fun input : ({coordinate : List (Fin rule.edges) × Bool //
      coordinate.1.length < address.length} → Configuration rule.edges) =>
    actualLiveIndicatorCompletion rule word (innovationPrefixFill rule address.length input)
  have historyMeasurable : Measurable historyIndicator :=
    (actualLiveIndicator_measurable_completion rule word).comp (innovationPrefixFill_measurable rule address.length)
  have factor (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
      historyIndicator (fun coordinate => marks coordinate.val) =
        actualLiveIndicatorCompletion rule word marks := by
    have same : retainedComponentState rule
        (innovationPrefixFill rule address.length (fun coordinate => marks coordinate.val)) word =
      retainedComponentState rule marks word := by
      apply retainedComponentStateFrom_congr_prefix_completion
      intro location opened shorter
      simp only [List.length_nil, zero_add] at shorter
      simp only [innovationPrefixFill, dif_pos (shorter.trans_le longer)]
    simp only [historyIndicator, actualLiveIndicatorCompletion, same]
  have vector := actual_mass_continuation_prefix_independent_completion
    rule p positive belowOne fixedPoint continuation address
  have independent : IndepFun (actualLiveIndicatorCompletion rule word)
      (fun marks => continuation.mass parent (innovationTreeShift rule address marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    simpa only [Function.comp_def, factor] using vector.comp historyMeasurable (measurable_pi_apply parent)
  have shiftedIntegrable : Integrable (fun marks => continuation.mass parent (innovationTreeShift rule address marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).integrable_comp
      (continuation.measurable parent).aestronglyMeasurable |>.mpr (continuation.integrable parent)
  have shiftedMean : (∫ marks, continuation.mass parent (innovationTreeShift rule address marks)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) =
      ∫ marks, continuation.mass parent marks ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
    have transport := integral_map_of_stronglyMeasurable
      (μ := independentInnovationLaw rule p positive belowOne fixedPoint)
      (innovationTreeShift_measurable rule address) (continuation.measurable parent).stronglyMeasurable
    rw [(innovationTreeShift_preserving rule p positive belowOne fixedPoint address).map_eq] at transport
    exact transport.symm
  refine ⟨independent.integrable_mul
    (actualLiveIndicator_integrable_completion rule word _) shiftedIntegrable, ?_⟩
  rw [independent.integral_fun_mul_eq_mul_integral
    (actualLiveIndicator_measurable_completion rule word).aestronglyMeasurable
    ((continuation.measurable parent).comp (innovationTreeShift_measurable rule address)).aestronglyMeasurable,
    shiftedMean]

/-- The physical descendant sockets touching one planted terminal. -/
def actualTerminalSocketSetCompletion (rule : Rule) (fine depth : ℕ) (side : Bool) :
    Finset (Fin depth → Fin rule.edges) := by
  classical
  exact Finset.univ.filter (fun word => ∃ vertex : Fin (rule.generation fine).vertices,
    (generationComponentWordEmbedding rule fine depth word).vertex vertex =
      (rule.generation (fine + depth)).network.terminalVertex side)

/-- An unnormalised mass envelope for the actual terminal collar. Every live
coarse component contributes only descendants incident with its two physical
planted terminals. Original oriented continuations dominate every selected
descendant mask, keeping their coupling intact. -/
def actualTerminalCollarEnvelopeCompletion
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion rule p positive belowOne fixedPoint)
    (fine coarseDepth collarDepth : ℕ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  ∑ word : Fin coarseDepth → (Fin rule.edges × Bool), ∑ side : Bool,
    ∑ suffix ∈ actualTerminalSocketSetCompletion rule fine collarDepth side,
      ∑ parent : OrientedState,
        actualLiveIndicatorCompletion rule (List.ofFn word) marks * continuation.mass parent
          (innovationTreeShift rule (componentEdgeAddress (List.ofFn word) ++ List.ofFn suffix) marks)

end
end IGSIII34.Spectral
