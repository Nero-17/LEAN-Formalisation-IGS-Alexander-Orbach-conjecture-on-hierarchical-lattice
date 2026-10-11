import Universality.Percolation.PostexitSubcriticalBound
import Universality.Percolation.FiniteVertexMomentBound
import Universality.Percolation.UniformGenerationVolume

namespace Universality.Rule
noncomputable section

theorem Classical.postexit_birth_volume_bound {rule : Rule} (h : rule.Classical)
    (order : ℕ) (horder : 1 ≤ order) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ p exitParameter : ℝ, 0 < p → p < 1 →
      0 < exitParameter → exitParameter < 1 → ∀ offset : ℕ,
      rule.network.reliability^[offset] p = exitParameter → ∀ scale : ℝ, 1 ≤ scale →
      (∀ state k, k ≤ order → (rule.generation offset).network.conditionalVertexMoment p state k ≤
        scale ^ k * rule.network.conditionalVertexMoment exitParameter state k) → ∀ n : ℕ,
        rule.expectedClusterBirthPower p order (offset + n + 1) ≤
          bound * scale ^ order * (rule.edges : ℝ) ^ (order * n) := by
  obtain ⟨volume, hvolume, hvol⟩ := h.generation_volume_uniform_bound
  have hedges : (1 : ℝ) ≤ rule.edges := by have := h.edges_gt_one; exact_mod_cast (by omega : 1 ≤ rule.edges)
  have hvertices : (0 : ℝ) < rule.vertices := by have := h.vertices_gt_two; exact_mod_cast (by omega : 0 < rule.vertices)
  refine ⟨((rule.edges : ℝ) + 1) ^ (order - 1) *
    ((rule.vertices : ℝ) ^ order + (rule.edges : ℝ) * volume ^ order), by positivity, ?_⟩
  intro p exitParameter hp hp' hexit hexit' offset hparameter scale hscale hbase n
  have hcoarseBound : (rule.generation n).network.expectedInternalBoundaryMoment exitParameter order ≤
      volume ^ order * (rule.edges : ℝ) ^ (order * n) := by
    calc
      _ ≤ ((rule.generation n).vertices : ℝ) ^ order :=
        (rule.generation n).network.expectedInternalBoundaryMoment_le_vertices_pow hexit.le hexit'.le order
      _ ≤ (volume * (rule.edges : ℝ) ^ n) ^ order := pow_le_pow_left₀ (Nat.cast_nonneg _) (hvol n) _
      _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm n order]
  have hfineBound := (h.postexit_boundary_moment_comparison p exitParameter hp hp' hexit hexit'
    offset hparameter scale hscale order hbase n).trans
      (mul_le_mul_of_nonneg_left hcoarseBound (pow_nonneg (zero_le_one.trans hscale) _))
  have hbirth := rule.network.expectedBirthClusterPower_le_boundary_moment
    (rule.generation (offset + n)).network hp.le hp'.le order horder
  change rule.expectedClusterBirthPower p order (offset + n + 1) ≤ _ at hbirth
  apply hbirth.trans
  have hdegreePower := one_le_pow₀ (n := order * n) hedges
  have hscalePower := one_le_pow₀ (n := order) hscale
  have hbothPower : 1 ≤ scale ^ order * (rule.edges : ℝ) ^ (order * n) :=
    hscalePower.trans (le_mul_of_one_le_right (zero_le_one.trans hscalePower) hdegreePower)
  have hvertexTerm := mul_le_mul_of_nonneg_left hbothPower (pow_nonneg hvertices.le order)
  have hboundaryTerm := mul_le_mul_of_nonneg_left hfineBound (zero_le_one.trans hedges)
  have hinside : (rule.vertices : ℝ) ^ order + (rule.edges : ℝ) *
      (rule.generation (offset + n)).network.expectedInternalBoundaryMoment p order ≤
      ((rule.vertices : ℝ) ^ order + (rule.edges : ℝ) * volume ^ order) * scale ^ order *
        (rule.edges : ℝ) ^ (order * n) := by nlinarith
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hinside
    (pow_nonneg (by positivity : (0 : ℝ) ≤ (rule.edges : ℝ) + 1) _)

end
end Universality.Rule
