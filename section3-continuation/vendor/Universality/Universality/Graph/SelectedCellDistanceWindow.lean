import Universality.Graph.CellPairDistance
import Universality.Analysis.WindowScaleChoice
import Universality.Graph.GeodesicEdgeLevels
import Universality.Graph.GenerationDiameter

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Two fixed coarse cells have every cross pair in the requested distance
window, uniformly over all finer generations. The same coarse depth makes
the child diameter smaller than the lower endpoint of that window. -/
theorem Classical.exists_cell_distance_window {rule : Rule} (h : rule.Classical)
    (diameter : ℕ)
    (hdiameter : ∀ n (u v : Fin (rule.generation n).vertices),
      (rule.generation n).network.fullGraph.dist u v ≤
        diameter * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n)
    (lower upper : ℝ) (hlower : 0 < lower) (horder : lower < upper) (hupper : upper < 1) :
    ∃ coarse : ℕ, ∃ first second : Fin (rule.generation coarse).edges, first ≠ second ∧
      (∀ fine : ℕ, (diameter : ℝ) *
        (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ fine <
          lower * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^
            (coarse + fine + 2)) ∧
      ∀ fine (u v : Fin (rule.generation fine).vertices),
        lower * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^
            (coarse + fine + 2) ≤
          (((rule.generation coarse).network.substitute (rule.generation fine).network).fullGraph.dist
            ((rule.generation coarse).network.cellEmbedding (rule.generation fine).network first u)
            ((rule.generation coarse).network.cellEmbedding (rule.generation fine).network second v) : ℝ) ∧
        (((rule.generation coarse).network.substitute (rule.generation fine).network).fullGraph.dist
            ((rule.generation coarse).network.cellEmbedding (rule.generation fine).network first u)
            ((rule.generation coarse).network.cellEmbedding (rule.generation fine).network second v) : ℝ) ≤
          upper * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^
            (coarse + fine + 2) := by
  let length := rule.network.fullGraph.dist rule.network.source rule.network.target
  have hlength : 2 ≤ length := h.scale
  have hlengthReal : (1 : ℝ) ≤ length := by exact_mod_cast (show 1 ≤ length by omega)
  obtain ⟨coarse, index, hindex, hterminal, hleft, hfirstMargin, hsecondMargin⟩ :=
    exists_power_window_level length hlength lower upper hlower horder hupper (3 + 2 * diameter)
  have hterminal' : index < (rule.generation coarse).network.fullGraph.dist
      (rule.generation coarse).network.source (rule.generation coarse).network.target := by
    rw [rule.generation_terminal_distance (h.connected _) coarse]
    exact hterminal
  obtain ⟨first, second, hdistinct, hanchorLower, hanchorUpper⟩ :=
    (rule.generation coarse).network.exists_separated_geodesic_edges
      (h.generation coarse).connected index hindex hterminal'
  have hanchorLowerReal : (index : ℝ) ≤
      ((rule.generation coarse).network.fullGraph.dist
        ((rule.generation coarse).network.endpoint first).1
        ((rule.generation coarse).network.endpoint second).1 : ℝ) + 1 := by
    exact_mod_cast hanchorLower
  have hanchorUpperReal :
      ((rule.generation coarse).network.fullGraph.dist
        ((rule.generation coarse).network.endpoint first).1
        ((rule.generation coarse).network.endpoint second).1 : ℝ) ≤ (index : ℝ) + 2 := by
    exact_mod_cast hanchorUpper
  have hfirstMargin' : lower * (length : ℝ) ^ (coarse + 1) +
      (3 + 2 * (diameter : ℝ)) < index := by exact_mod_cast hfirstMargin
  have hsecondMargin' : (index : ℝ) + (3 + 2 * (diameter : ℝ)) <
      upper * (length : ℝ) ^ (coarse + 1) := by exact_mod_cast hsecondMargin
  have hleft' : 3 + 2 * (diameter : ℝ) < lower * (length : ℝ) ^ (coarse + 1) := by
    exact_mod_cast hleft
  have hscale (fine : ℕ) : 0 < (length : ℝ) ^ (fine + 1) :=
    pow_pos (zero_lt_one.trans_le hlengthReal) _
  have hdiameterScale (fine : ℕ) : (diameter : ℝ) * (length : ℝ) ^ fine ≤
      (diameter : ℝ) * (length : ℝ) ^ (fine + 1) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [pow_succ]
    exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hlengthReal) _) hlengthReal
  have hcombined (fine : ℕ) : (length : ℝ) ^ (coarse + fine + 2) =
      (length : ℝ) ^ (coarse + 1) * (length : ℝ) ^ (fine + 1) := by
    rw [← pow_add]
    congr 1
    omega
  refine ⟨coarse, first, second, hdistinct, ?_, ?_⟩
  · intro fine
    change (diameter : ℝ) * (length : ℝ) ^ fine < lower * (length : ℝ) ^ (coarse + fine + 2)
    rw [hcombined]
    have hmargin := mul_lt_mul_of_pos_right hleft' (hscale fine)
    have hdiam := hdiameterScale fine
    have hd : (0 : ℝ) ≤ diameter := Nat.cast_nonneg _
    have hs := hscale fine
    nlinarith
  · intro fine u v
    have hpair := (rule.generation coarse).network.substituted_cell_pair_distance_bounds
      (rule.generation fine).network (h.generation coarse).connected (h.generation fine).connected
      (diameter * length ^ fine) (hdiameter fine) first second u v
    rw [rule.generation_terminal_distance (h.connected _) fine] at hpair
    have hpairLower :
        ((rule.generation coarse).network.fullGraph.dist
          ((rule.generation coarse).network.endpoint first).1
          ((rule.generation coarse).network.endpoint second).1 : ℝ) * (length : ℝ) ^ (fine + 1) ≤
        (((rule.generation coarse).network.substitute (rule.generation fine).network).fullGraph.dist
          ((rule.generation coarse).network.cellEmbedding (rule.generation fine).network first u)
          ((rule.generation coarse).network.cellEmbedding (rule.generation fine).network second v) : ℝ) +
            2 * ((diameter : ℝ) * (length : ℝ) ^ fine) := by
      have hh := hpair.1
      exact_mod_cast hh
    have hpairUpper :
        (((rule.generation coarse).network.substitute (rule.generation fine).network).fullGraph.dist
          ((rule.generation coarse).network.cellEmbedding (rule.generation fine).network first u)
          ((rule.generation coarse).network.cellEmbedding (rule.generation fine).network second v) : ℝ) ≤
        ((rule.generation coarse).network.fullGraph.dist
          ((rule.generation coarse).network.endpoint first).1
          ((rule.generation coarse).network.endpoint second).1 : ℝ) * (length : ℝ) ^ (fine + 1) +
            2 * ((diameter : ℝ) * (length : ℝ) ^ fine) := by
      have hh := hpair.2
      exact_mod_cast hh
    have hfirstScaled := mul_lt_mul_of_pos_right hfirstMargin' (hscale fine)
    have hsecondScaled := mul_lt_mul_of_pos_right hsecondMargin' (hscale fine)
    have hanchorLowerScaled := mul_le_mul_of_nonneg_right hanchorLowerReal (hscale fine).le
    have hanchorUpperScaled := mul_le_mul_of_nonneg_right hanchorUpperReal (hscale fine).le
    have hdiam := hdiameterScale fine
    have hs := hscale fine
    change lower * (length : ℝ) ^ (coarse + fine + 2) ≤ _ ∧
      _ ≤ upper * (length : ℝ) ^ (coarse + fine + 2)
    rw [hcombined]
    constructor <;> nlinarith

end
end Universality.Rule
