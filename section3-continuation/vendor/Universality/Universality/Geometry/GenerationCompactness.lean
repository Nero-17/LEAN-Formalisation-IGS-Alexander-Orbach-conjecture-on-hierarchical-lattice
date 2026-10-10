import Universality.Geometry.GenerationNet
import Universality.Geometry.GeometricNets

namespace Universality.Rule
noncomputable section
open Set

/-- The complete realisation of the actual rescaled generation metrics is
compact. No bounded-degree assumption or Hausdorff-dimension premise is used. -/
theorem Classical.exists_compact_generation_metric {rule : Rule} (h : rule.Classical) :
    ∃ (Ambient : Type) (metric : MetricSpace Ambient),
      letI := metric
      CompleteSpace Ambient ∧ CompactSpace Ambient ∧
      ∃ inclusion : (depth : ℕ) → Fin (rule.generation depth).vertices → Ambient,
        (∀ depth first second,
          dist (inclusion depth first) (inclusion depth second) =
            scaledGenerationDistance rule depth first second) ∧
        (∀ depth vertex, inclusion depth vertex =
          inclusion (depth + 1) (rule.generationOldVertex depth vertex)) ∧
        Dense (⋃ depth, Set.range (inclusion depth)) := by
  obtain ⟨Ambient, metric, hcomplete, inclusion, hdistance, hcompatible, hdense⟩ :=
    h.exists_complete_generation_metric
  letI := metric
  letI : CompleteSpace Ambient := hcomplete
  let radius := Finset.univ.sup (fun vertex =>
    rule.network.fullGraph.dist rule.network.source vertex)
  have hradius (vertex) : rule.network.fullGraph.dist rule.network.source vertex ≤ radius :=
    Finset.le_sup (Finset.mem_univ vertex)
  let ratio : ℝ := (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ)⁻¹
  let constant : ℝ := (radius : ℝ) /
    (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ 2
  have hratio : 0 ≤ ratio := inv_nonneg.mpr h.scale_real_pos.le
  have hratioOne : ratio < 1 :=
    (inv_lt_one₀ h.scale_real_pos).mpr (by exact_mod_cast h.scale)
  have hconstant : 0 ≤ constant := by dsimp [constant]; positivity
  have hnested : Monotone (fun depth => Set.range (inclusion depth)) := by
    apply monotone_nat_of_le_succ
    intro depth point hpoint
    obtain ⟨vertex, rfl⟩ := hpoint
    exact ⟨rule.generationOldVertex depth vertex, (hcompatible depth vertex).symm⟩
  have hstep (depth) (point : Fin (rule.generation (depth + 1)).vertices) :
      ∃ previous : Fin (rule.generation depth).vertices,
        dist (inclusion (depth + 1) point) (inclusion depth previous) ≤ constant * ratio ^ depth := by
    obtain ⟨previous, hprevious⟩ := h.generation_vertex_near_old radius hradius depth point
    refine ⟨previous, ?_⟩
    calc
      dist (inclusion (depth + 1) point) (inclusion depth previous) =
          scaledGenerationDistance rule (depth + 1) (rule.generationOldVertex depth previous) point := by
            rw [hcompatible depth previous, dist_comm, hdistance]
      _ ≤ (radius : ℝ) /
          (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (depth + 2) := hprevious
      _ = constant * ratio ^ depth := by
        simp [constant, ratio, pow_add, div_eq_mul_inv, mul_comm, mul_left_comm]
  have hbounded := Geometry.totallyBounded_union_of_geometric_steps
    (fun depth => Fin (rule.generation depth).vertices) inclusion hnested
    constant ratio hconstant hratio hratioOne hstep
  have hcompact := hbounded.closure.isCompact_of_isClosed isClosed_closure
  rw [hdense.closure_eq] at hcompact
  exact ⟨Ambient, metric, hcomplete, isCompact_univ_iff.mp hcompact,
    inclusion, hdistance, hcompatible, hdense⟩

end
end Universality.Rule

