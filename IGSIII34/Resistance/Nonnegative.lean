import IGSIII34.Resistance.Lipschitz

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem isCompact_bounded_unitFlows (network : FiniteNetwork Vertex Edge) :
    IsCompact {current : Edge → ℝ | current ∈ network.unitFlows ∧
      ∀ edge, |current edge| ≤ 1} := by
  have compactBox : IsCompact {current : Edge → ℝ |
      ∀ edge, current edge ∈ Set.Icc (-1) 1} :=
    isCompact_pi_infinite (fun _ => isCompact_Icc)
  have closedBounds : IsClosed {current : Edge → ℝ | ∀ edge, |current edge| ≤ 1} := by
    simpa only [Set.setOf_forall] using isClosed_iInter
      (fun edge => isClosed_le (continuous_apply edge).abs continuous_const)
  apply compactBox.of_isClosed_subset (network.isClosed_unitFlows.inter closedBounds)
  intro current membership edge
  exact abs_le.mp (membership.2 edge)

theorem exists_bounded_minimizing_unitFlow_of_nonnegative
    (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {resistance : Edge → ℝ} (nonnegative : ∀ edge, 0 ≤ resistance edge) :
    ∃ current ∈ network.unitFlows, (∀ edge, |current edge| ≤ 1) ∧
      energy resistance current = network.effectiveResistance resistance := by
  obtain ⟨trialCurrent, trialFlow, trialMinimal⟩ :=
    network.exists_minimizing_unitFlow_of_connected connected (fun _ => zero_lt_one)
  have trialBound := network.minimizing_current_abs_le_one (fun _ => zero_lt_one)
    trialFlow trialMinimal
  obtain ⟨current, membership, minimal⟩ := network.isCompact_bounded_unitFlows.exists_isMinOn
    ⟨trialCurrent, trialFlow, trialBound⟩ (continuous_energy resistance).continuousOn
  refine ⟨current, membership.1, membership.2, le_antisymm ?_ ?_⟩
  · apply network.le_effectiveResistance (network.unitFlows_nonempty_of_connected connected)
    intro competitor competitorFlow
    apply le_of_forall_pos_le_add
    intro tolerance tolerancePositive
    have competitorEnergyNonnegative : 0 ≤ energy (fun _ => 1) competitor :=
      energy_nonneg (fun _ => zero_le_one) competitor
    have denominatorPositive : 0 < energy (fun _ => 1) competitor + 1 := by positivity
    have perturbationPositive : 0 < tolerance / (energy (fun _ => 1) competitor + 1) :=
      div_pos tolerancePositive denominatorPositive
    have perturbedPositive (edge : Edge) :
        0 < resistance edge + tolerance / (energy (fun _ => 1) competitor + 1) :=
      add_pos_of_nonneg_of_pos (nonnegative edge) perturbationPositive
    obtain ⟨perturbedCurrent, perturbedFlow, perturbedMinimal⟩ :=
      network.exists_minimizing_unitFlow_of_connected connected perturbedPositive
    have perturbedBound := network.minimizing_current_abs_le_one perturbedPositive
      perturbedFlow perturbedMinimal
    have comparison := (minimal ⟨perturbedFlow, perturbedBound⟩).trans
      ((energy_mono (fun edge => le_add_of_nonneg_right perturbationPositive.le)
        perturbedCurrent).trans
        (perturbedMinimal.le.trans
          (network.effectiveResistance_le_energy (fun edge => (perturbedPositive edge).le)
            competitorFlow)))
    have energyIdentity :
        energy (fun edge => resistance edge + tolerance / (energy (fun _ => 1) competitor + 1))
          competitor = energy resistance competitor +
            tolerance / (energy (fun _ => 1) competitor + 1) * energy (fun _ => 1) competitor := by
      rw [energy_add]
      congr 1
      simpa only [mul_one] using energy_scale (fun _ : Edge => 1) competitor
        (tolerance / (energy (fun _ => 1) competitor + 1))
    rw [energyIdentity] at comparison
    have perturbationBound : tolerance / (energy (fun _ => 1) competitor + 1) *
        energy (fun _ => 1) competitor ≤ tolerance := by
      rw [div_mul_eq_mul_div, div_le_iff₀ denominatorPositive]
      nlinarith
    exact comparison.trans (add_le_add (le_refl _) perturbationBound)
  · exact network.effectiveResistance_le_energy nonnegative membership.1

theorem effectiveResistance_le_add_sum_abs_of_nonnegative
    (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {first second : Edge → ℝ}
    (firstNonnegative : ∀ edge, 0 ≤ first edge)
    (secondNonnegative : ∀ edge, 0 ≤ second edge) :
    network.effectiveResistance second ≤ network.effectiveResistance first +
      ∑ edge, |second edge - first edge| := by
  obtain ⟨current, unitFlow, currentBound, minimal⟩ :=
    network.exists_bounded_minimizing_unitFlow_of_nonnegative connected firstNonnegative
  calc
    _ ≤ energy second current := network.effectiveResistance_le_energy secondNonnegative unitFlow
    _ ≤ energy first current + ∑ edge, |second edge - first edge| :=
      trial_energy_difference_le_sum_abs first second current currentBound
    _ = _ := by rw [minimal]

theorem effectiveResistance_abs_sub_le_sum_abs_of_nonnegative
    (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    {first second : Edge → ℝ}
    (firstNonnegative : ∀ edge, 0 ≤ first edge)
    (secondNonnegative : ∀ edge, 0 ≤ second edge) :
    |network.effectiveResistance first - network.effectiveResistance second| ≤
      ∑ edge, |first edge - second edge| := by
  rw [abs_sub_le_iff]
  constructor
  · have bound := network.effectiveResistance_le_add_sum_abs_of_nonnegative connected
      secondNonnegative firstNonnegative
    linarith
  · have bound := network.effectiveResistance_le_add_sum_abs_of_nonnegative connected
      firstNonnegative secondNonnegative
    simp_rw [abs_sub_comm (second _) (first _)] at bound
    linarith

end
end IGSIII34.Resistance.FiniteNetwork
