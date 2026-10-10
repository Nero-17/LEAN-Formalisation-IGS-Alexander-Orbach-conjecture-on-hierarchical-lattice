import IGSIII34.Resistance.SmallEdges
import IGSIII34.Percolation.ElectricalTransfer

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Percolation
noncomputable section
open Resistance Resistance.FiniteNetwork Universality Universality.FiniteNetwork

def smallConfiguration {edges : ℕ} (configuration : Configuration edges)
    (input : Fin edges → ℝ) (threshold : ℝ) : Configuration edges :=
  fun edge => configuration edge && decide (input edge ≤ threshold)

theorem smallEdgeGraph_eq_openGraph {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (input : Fin edges → ℝ) (threshold : ℝ) :
    (network rule configuration).smallEdgeGraph (fun edge => input edge.val) threshold =
      rule.openGraph (smallConfiguration configuration input threshold) := by
  ext first second
  constructor
  · rintro ⟨different, edge, small, orientation⟩
    refine ⟨different, edge.val, ?_, orientation⟩
    simp only [smallConfiguration, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨edge.property, small⟩
  · rintro ⟨different, edge, opened, orientation⟩
    have parts : configuration edge = true ∧ input edge ≤ threshold := by
      simpa only [smallConfiguration, Bool.and_eq_true, decide_eq_true_eq] using opened
    exact ⟨different, ⟨edge, parts.1⟩, parts.2, orientation⟩

theorem electricalCell_smallConfiguration_crosses {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (crosses : rule.crosses configuration = true)
    {input : Fin edges → ℝ} (nonnegative : ∀ edge, 0 ≤ input edge)
    {bound : ℝ} (boundPositive : 0 < bound)
    (resistanceBound : electricalCell rule configuration input ≤ bound) :
    rule.crosses (smallConfiguration configuration input ((edges : ℝ) * bound)) = true := by
  have reachable := (network rule configuration).smallEdgeGraph_connected_of_resistance_le
    (connected_of_crosses _ _ crosses) (fun edge => nonnegative edge.val) boundPositive resistanceBound
  rw [smallEdgeGraph_eq_openGraph] at reachable
  have cardBound : (Fintype.card {edge : Fin edges // configuration edge = true} : ℝ) ≤ edges := by
    exact_mod_cast (show Fintype.card {edge : Fin edges // configuration edge = true} ≤ edges from
      by simpa using Fintype.card_subtype_le (fun edge : Fin edges => configuration edge = true))
  apply (rule.crosses_eq_true _).mpr
  exact reachable.mono (by
    intro first second adjacent
    rcases adjacent with ⟨different, edge, opened, orientation⟩
    have parts : configuration edge = true ∧ input edge ≤
        (Fintype.card {edge : Fin edges // configuration edge = true} : ℝ) * bound := by
      simpa only [smallConfiguration, Bool.and_eq_true, decide_eq_true_eq] using opened
    refine ⟨different, edge, ?_, orientation⟩
    simp only [smallConfiguration, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨parts.1, parts.2.trans (mul_le_mul_of_nonneg_right cardBound boundPositive.le)⟩)

end
end IGSIII34.Percolation
