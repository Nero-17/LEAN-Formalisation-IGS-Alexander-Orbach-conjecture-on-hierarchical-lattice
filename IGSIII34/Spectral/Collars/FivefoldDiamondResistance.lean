import IGSIII34.Spectral.Collars.FivefoldDiamondGraph
import IGSIII34.Resistance.DistanceEnergy
import IGSIII34.Percolation.ElectricalTransfer
import IGSIII34.Percolation.Continuation.NaturalResistanceCompletion
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Resistance
open IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped BigOperators _root_.Topology

theorem fivefoldDiamond_integer_divergence (vertex : Fin 20) :
    (∑ edge : Fin 20, ((if (fivefoldDiamondNetwork.endpoint edge).1 = vertex then 1 else 0) -
      (if (fivefoldDiamondNetwork.endpoint edge).2 = vertex then 1 else 0) : ℤ)) =
      2 * ((if vertex = 0 then 1 else 0) - (if vertex = 1 then 1 else 0)) := by
  have certificate : ∀ vertex : Fin 20,
    (∑ edge : Fin 20, ((if (fivefoldDiamondNetwork.endpoint edge).1 = vertex then 1 else 0) -
      (if (fivefoldDiamondNetwork.endpoint edge).2 = vertex then 1 else 0) : ℤ)) =
      2 * ((if vertex = 0 then 1 else 0) - (if vertex = 1 then 1 else 0)) := by decide
  exact certificate vertex

theorem fivefoldDiamond_unit_current :
    (fun _ : Fin 20 => (1 / 2 : ℝ)) ∈ (ofIGSII fivefoldDiamondNetwork).unitFlows := by
  intro vertex
  have cast := congrArg (fun value : ℤ => (value : ℝ)) (fivefoldDiamond_integer_divergence vertex)
  push_cast at cast
  change (∑ edge : Fin 20, (1 / 2 : ℝ) *
      ((if (fivefoldDiamondNetwork.endpoint edge).1 = vertex then 1 else 0) -
       (if (fivefoldDiamondNetwork.endpoint edge).2 = vertex then 1 else 0))) =
    (if vertex = 0 then 1 else 0) - (if vertex = 1 then 1 else 0)
  rw [← Finset.mul_sum, cast]
  ring

theorem fivefoldDiamond_full_open_resistance :
    (ofIGSII fivefoldDiamondNetwork).effectiveResistance (fun _ => 1) = 5 := by
  have connected : (ofIGSII fivefoldDiamondNetwork).graph.Reachable
      (ofIGSII fivefoldDiamondNetwork).source (ofIGSII fivefoldDiamondNetwork).target := by
    rw [ofIGSII_graph]
    exact fivefoldDiamondRule_classical.connected _
  have lower := (ofIGSII fivefoldDiamondNetwork).distance_sq_le_edge_count_mul_unitResistance connected
  have distance : (ofIGSII fivefoldDiamondNetwork).graph.dist
      (ofIGSII fivefoldDiamondNetwork).source (ofIGSII fivefoldDiamondNetwork).target = 10 := by
    rw [ofIGSII_graph]
    exact fivefoldDiamond_terminal_distance
  rw [distance] at lower
  have upper := (ofIGSII fivefoldDiamondNetwork).effectiveResistance_le_energy
    (fun _ => zero_le_one) fivefoldDiamond_unit_current
  norm_num [Resistance.FiniteNetwork.energy] at lower upper
  nlinarith

theorem fivefoldDiamond_full_open_IGSII_resistance :
    fivefoldDiamondNetwork.unitEffectiveResistance (fivefoldDiamondRule_classical.connected _) = 5 := by
  rw [← ofIGSII_unitEffectiveResistance]
  exact fivefoldDiamond_full_open_resistance

theorem fivefoldDiamond_configuration_resistance_lower
    (configuration : Configuration 20) (crossing : fivefoldDiamondNetwork.crosses configuration = true) :
    5 ≤ unitConfigurationResistance fivefoldDiamondNetwork configuration := by
  have connected := connected_of_crosses fivefoldDiamondNetwork configuration crossing
  have distance := ((fivefoldDiamondNetwork.crosses_eq_true configuration).mp crossing).dist_anti
    (fivefoldDiamondNetwork.openGraph_le_full configuration)
  rw [fivefoldDiamond_terminal_distance] at distance
  have realDistance : (10 : ℝ) ≤ (network fivefoldDiamondNetwork configuration).graph.dist
      fivefoldDiamondNetwork.source fivefoldDiamondNetwork.target := by
    rw [graph_eq_openGraph]
    exact_mod_cast distance
  have lower := (network fivefoldDiamondNetwork configuration).distance_sq_le_edge_count_mul_unitResistance connected
  have count : (Fintype.card {edge : Fin 20 // configuration edge = true} : ℝ) ≤ 20 := by
    exact_mod_cast (show Fintype.card {edge : Fin 20 // configuration edge = true} ≤ 20 by
      simpa using Fintype.card_subtype_le (fun edge : Fin 20 => configuration edge = true))
  have nonnegative := (network fivefoldDiamondNetwork configuration).effectiveResistance_nonneg
    ((network fivefoldDiamondNetwork configuration).unitFlows_nonempty_of_connected connected) (fun _ => zero_le_one)
  have bound := mul_le_mul_of_nonneg_right count nonnegative
  have square : (100 : ℝ) ≤ ((network fivefoldDiamondNetwork configuration).graph.dist
      fivefoldDiamondNetwork.source fivefoldDiamondNetwork.target : ℝ)^2 := by
    nlinarith [sq_nonneg (((network fivefoldDiamondNetwork configuration).graph.dist
      fivefoldDiamondNetwork.source fivefoldDiamondNetwork.target : ℝ) - 10)]
  change 5 ≤ (network fivefoldDiamondNetwork configuration).effectiveResistance (fun _ => 1)
  change ((network fivefoldDiamondNetwork configuration).graph.dist
      fivefoldDiamondNetwork.source fivefoldDiamondNetwork.target : ℝ)^2 ≤ _ at lower
  nlinarith

theorem fivefoldDiamond_electrical_iteration_lower
    (marks : (List (Fin 20) × Bool) → Configuration 20)
    (crossing : ∀ address, fivefoldDiamondNetwork.crosses (marks (address,true)) = true)
    (depth : ℕ) (address : List (Fin 20)) :
    (5 : ℝ)^depth ≤ electricalIteration fivefoldDiamondRule marks depth address := by
  induction depth generalizing address with
  | zero => simp [electricalIteration]
  | succ depth inductionHypothesis =>
    change (5 : ℝ)^(depth+1) ≤ electricalCell fivefoldDiamondNetwork (marks (address,true))
      (fun edge => electricalIteration fivefoldDiamondRule marks depth (address ++ [edge]))
    have lower := fivefoldDiamond_configuration_resistance_lower (marks (address,true)) (crossing address)
    have monotone := electricalCell_monotone fivefoldDiamondNetwork (marks (address,true))
      (first := fun _ => (5 : ℝ)^depth)
      (fun _ => (pow_pos (by norm_num : (0 : ℝ) < 5) depth).le) (fun edge => inductionHypothesis (address ++ [edge]))
    have scaling := electricalCell_scale fivefoldDiamondNetwork (marks (address,true))
      (input := fun _ => 1) (fun _ => zero_le_one) (scalar := (5 : ℝ)^depth)
      (pow_pos (by norm_num : (0 : ℝ) < 5) depth).le
    simp only [mul_one] at scaling
    rw [scaling] at monotone
    calc
      (5 : ℝ)^(depth+1) = (5 : ℝ)^depth * 5 := pow_succ _ _
      _ ≤ (5 : ℝ)^depth * unitConfigurationResistance fivefoldDiamondNetwork (marks (address,true)) :=
        mul_le_mul_of_nonneg_left lower (pow_pos (by norm_num : (0 : ℝ) < 5) depth).le
      _ ≤ _ := monotone

theorem fivefoldDiamond_natural_resistance_growth_lower
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : fivefoldDiamondRule.network.reliability p = p)
    (natural : NaturalResistanceCompletion fivefoldDiamondRule p positive belowOne fixedPoint) :
    5 ≤ natural.growth := by
  have events : ∀ᵐ marks ∂independentInnovationLaw fivefoldDiamondRule p positive belowOne fixedPoint,
      (∀ address, fivefoldDiamondNetwork.crosses (marks (address,true)) = true) ∧
      Tendsto (fun depth => natural.growth⁻¹^depth * electricalIteration fivefoldDiamondRule marks depth [])
        atTop (𝓝 (natural.amplitude * electricalField fivefoldDiamondRule p positive belowOne fixedPoint natural.field [] marks)) := by
    filter_upwards [independentInnovationLaw_crosses fivefoldDiamondRule p positive belowOne fixedPoint, natural.almostSure]
      with marks crossing convergence
    exact ⟨fun address => crossing address true, convergence []⟩
  obtain ⟨marks, crossing, convergence⟩ := events.exists
  by_contra smaller
  have growthPositive := zero_lt_one.trans natural.aboveOne
  have ratioGreater : 1 < (5 : ℝ) / natural.growth := (one_lt_div growthPositive).mpr (lt_of_not_ge smaller)
  have diverges := tendsto_pow_atTop_atTop_of_one_lt ratioGreater
  have upper := convergence.eventually (eventually_lt_nhds
    (lt_add_one (natural.amplitude * electricalField fivefoldDiamondRule p positive belowOne fixedPoint natural.field [] marks)))
  have large := diverges.eventually (eventually_ge_atTop
    (natural.amplitude * electricalField fivefoldDiamondRule p positive belowOne fixedPoint natural.field [] marks + 1))
  obtain ⟨depth, smaller, larger⟩ := (upper.and large).exists
  have lower := mul_le_mul_of_nonneg_left (fivefoldDiamond_electrical_iteration_lower marks crossing depth [])
    (pow_pos (inv_pos.mpr growthPositive) depth).le
  have identity : natural.growth⁻¹^depth * (5 : ℝ)^depth = ((5 : ℝ) / natural.growth)^depth := by
    rw [← mul_pow, div_eq_mul_inv, mul_comm]
  rw [identity] at lower
  exact (not_lt_of_ge (larger.trans lower)) smaller

end
end IGSIII34.Spectral
