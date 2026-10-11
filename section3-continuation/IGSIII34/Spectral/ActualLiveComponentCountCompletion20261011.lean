import IGSIII34.Spectral.LiveComponentCountCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

namespace IGSIII34.Spectral
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open MeasureTheory Filter Matrix
open scoped BigOperators Topology

theorem incident_edge_of_reachable_completion20261011 {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (first last : Fin vertices)
    (distinct : first ≠ last) (reachable : network.fullGraph.Reachable first last) :
    ∃ edge, (network.endpoint edge).1 = first ∨ (network.endpoint edge).2 = first := by
  obtain ⟨walk⟩ := reachable
  cases walk with
  | nil => exact (distinct rfl).elim
  | cons adjacency tail =>
      obtain ⟨_, edge, _, pair | pair⟩ := adjacency
      · exact ⟨edge, Or.inl (congrArg Prod.fst pair)⟩
      · exact ⟨edge, Or.inr (congrArg Prod.snd pair)⟩

theorem classical_terminal_incident_completion20261011 (rule : Rule)
    (classicalRule : rule.Classical) :
    (∃ edge, (rule.network.endpoint edge).1 = rule.network.source ∨
      (rule.network.endpoint edge).2 = rule.network.source) ∧
    (∃ edge, (rule.network.endpoint edge).1 = rule.network.target ∨
      (rule.network.endpoint edge).2 = rule.network.target) := by
  constructor
  · exact incident_edge_of_reachable_completion20261011 rule.network rule.network.source
      rule.network.target rule.network.terminals_distinct (classicalRule.connected rule.network.target)
  · exact incident_edge_of_reachable_completion20261011 rule.network rule.network.target
      rule.network.source rule.network.terminals_distinct.symm (classicalRule.connected rule.network.target).symm

theorem componentSlotResponse_one_le_of_live_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (configuration : Configuration rule.edges)
    (parent : OrientedState) (live : parent ≠ .inactive) :
    1 ≤ componentSlotResponseCompletion20261011 rule.network configuration parent := by
  classical
  obtain ⟨sourceIncidence, targetIncidence⟩ := classical_terminal_incident_completion20261011 rule classicalRule
  have sourceReachable : (rule.network.openGraph configuration).reachableDecide
      rule.network.source rule.network.source = true :=
    (SimpleGraph.reachableDecide_eq_true _ _ _).mpr (SimpleGraph.Reachable.refl _)
  have targetReachable : (rule.network.openGraph configuration).reachableDecide
      rule.network.target rule.network.target = true :=
    (SimpleGraph.reachableDecide_eq_true _ _ _).mpr (SimpleGraph.Reachable.refl _)
  have selected : ∃ edge, rule.network.selectedActive parent.sourceSelected parent.targetSelected
      configuration (rule.network.endpoint edge).1 = true ∨
      rule.network.selectedActive parent.sourceSelected parent.targetSelected
        configuration (rule.network.endpoint edge).2 = true := by
    cases parent with
    | inactive => exact (live rfl).elim
    | connected | both | sourceOnly =>
        obtain ⟨edge, first | last⟩ := sourceIncidence
        · exact ⟨edge, Or.inl (by simp [first, OrientedState.sourceSelected,
            OrientedState.targetSelected, selectedActive, sourceReachable])⟩
        · exact ⟨edge, Or.inr (by simp [last, OrientedState.sourceSelected,
            OrientedState.targetSelected, selectedActive, sourceReachable])⟩
    | targetOnly =>
        obtain ⟨edge, first | last⟩ := targetIncidence
        · exact ⟨edge, Or.inl (by simp [first, OrientedState.sourceSelected,
            OrientedState.targetSelected, selectedActive, targetReachable])⟩
        · exact ⟨edge, Or.inr (by simp [last, OrientedState.sourceSelected,
            OrientedState.targetSelected, selectedActive, targetReachable])⟩
  obtain ⟨edge, active⟩ := selected
  have edgeBound : 1 ≤ componentSlotCountCompletion20261011
      (rule.network.orientedChildState parent.sourceSelected parent.targetSelected configuration edge) := by
    cases first : rule.network.selectedActive parent.sourceSelected parent.targetSelected configuration
        (rule.network.endpoint edge).1 <;>
      cases last : rule.network.selectedActive parent.sourceSelected parent.targetSelected configuration
        (rule.network.endpoint edge).2 <;>
      cases opened : configuration edge <;>
      simp_all [orientedChildState, orientedStateOf, componentSlotCountCompletion20261011]
  apply edgeBound.trans
  unfold componentSlotResponseCompletion20261011
  apply Finset.single_le_sum (s := Finset.univ) (a := edge)
    (f := fun other => componentSlotCountCompletion20261011
      (rule.network.orientedChildState parent.sourceSelected parent.targetSelected configuration other))
  · intro other _
    cases rule.network.orientedChildState parent.sourceSelected parent.targetSelected configuration other <;>
      norm_num [componentSlotCountCompletion20261011]
  · exact Finset.mem_univ _

def actualLiveComponentCountCompletion20261011 (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) (depth : ℕ) : ℕ :=
  (Finset.univ.filter fun word : Fin depth → (Fin rule.edges × Bool) =>
    retainedComponentState rule marks (List.ofFn word) ≠ .inactive).card

theorem actualLiveComponentCount_le_slot_population_completion20261011
    (rule : Rule) (classicalRule : rule.Classical)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) :
    (actualLiveComponentCountCompletion20261011 rule marks depth : ℝ) ≤
      markedComponentSlotResponseCompletion20261011 rule marks depth [] .connected := by
  classical
  have partition := retainedComponentSlotResponse_partition_completion20261011 rule marks crossing 0 depth []
  simp only [Nat.zero_add, List.nil_append] at partition
  change markedComponentSlotResponseCompletion20261011 rule marks depth [] .connected = _ at partition
  rw [partition]
  simp only [actualLiveComponentCountCompletion20261011, Finset.card_eq_sum_ones,
    Finset.sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_le_sum
  intro word _
  by_cases live : retainedComponentState rule marks (List.ofFn word) ≠ .inactive
  · rw [if_pos live]
    exact componentSlotResponse_one_le_of_live_completion20261011 rule classicalRule _ _ live
  · rw [if_neg live]
    exact componentSlotResponse_nonnegative_completion20261011 _ _ _

def componentSlotLiveValuesCompletion20261011 : LiveState → ℝ
  | .both => 2
  | _ => 1

theorem componentSlotResponse_connected_eq_live_completion20261011 {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges)
    (crossing : network.crosses configuration = true) :
    componentSlotResponseCompletion20261011 network configuration .connected =
      network.liveResponse .connected configuration componentSlotLiveValuesCompletion20261011 := by
  have responseEquality : componentSlotResponseCompletion20261011 network configuration .connected =
      network.orientedResponse true true configuration
        (fun child => componentSlotLiveValuesCompletion20261011 child.erase) := by
    unfold componentSlotResponseCompletion20261011 orientedResponse
    apply Finset.sum_congr rfl
    intro edge _
    change componentSlotCountCompletion20261011 (network.orientedChildState true true configuration edge) = _
    cases network.orientedChildState true true configuration edge <;>
      rfl
  rw [responseEquality, network.orientedResponse_connected configuration crossing]
  simpa only [show (LiveState.connected == LiveState.both) = false from rfl] using
    network.orientedResponse_erase .connected configuration componentSlotLiveValuesCompletion20261011

theorem actual_live_component_count_Perron_bound_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ coefficient : ℝ, 0 < coefficient ∧ ∀ depth : ℕ,
        (actualLiveComponentCountCompletion20261011 rule marks depth : ℝ) ≤
          coefficient * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^depth := by
  obtain ⟨right, left, vertexCoefficient, limit, _, _, _, _, _, _, _, _, _, _, _, _, coordinates, _⟩ :=
    classicalRule.three_state_mass_perron p positive belowOne fixedPoint
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  rw [← independentInnovationLaw_history_path rule p positive belowOne fixedPoint [] true] at coordinates
  have actual := ae_of_ae_map (markedHistoryPath_measurable rule [] true).aemeasurable coordinates
  filter_upwards [actual, independentInnovationLaw_crosses rule p positive belowOne fixedPoint] with
    marks coordinates crossing
  have convergence := ((coordinates .connected).add ((coordinates .both).const_mul 2)).add (coordinates .single)
  obtain ⟨bound, bounded⟩ := convergence.bddAbove_range
  refine ⟨max 1 bound * (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal,
    mul_pos (zero_lt_one.trans_le (le_max_left _ _)) radiusPositive, ?_⟩
  intro depth
  apply (actualLiveComponentCount_le_slot_population_completion20261011 rule classicalRule marks crossing depth).trans
  simp only [markedComponentSlotResponseCompletion20261011, OrientedState.massOpened, decide_true]
  rw [
    componentSlotResponse_connected_eq_live_completion20261011 _ _
      (markedGenerationConfiguration_crosses rule marks crossing depth [] true)]
  have countBound := (bounded (Set.mem_range_self (depth + 1))).trans (le_max_right (1 : ℝ) bound)
  simp only [Rule.ConfigurationHistory.rootLevelPopulation_succ,
    Rule.ConfigurationHistory.weightedPopulation, markedHistoryPath,
    Rule.ConfigurationHistory.latest_ofFine, liveResponse_eq,
    mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one, mul_zero] at countBound
  rw [liveResponse_eq, sum_liveState]
  simp only [componentSlotLiveValuesCompletion20261011, mul_one]
  have bound := (div_le_iff₀ (pow_pos radiusPositive (depth + 1))).mp
    (show ((rule.generation depth).network.liveCount .connected .connected
        (markedGenerationConfiguration rule marks depth [] true) +
      2 * (rule.generation depth).network.liveCount .connected .both
        (markedGenerationConfiguration rule marks depth [] true) +
      (rule.generation depth).network.liveCount .connected .single
        (markedGenerationConfiguration rule marks depth [] true) : ℝ) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^(depth + 1) ≤ max 1 bound by
      convert countBound using 1
      all_goals
        first
        | rfl
        | simp only [add_div, mul_div_assoc])
  simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using bound

end
end IGSIII34.Spectral
