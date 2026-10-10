import Universality.Percolation.GenerationFirstMomentRecursion
import Universality.Percolation.PreexitMomentBounds
import Universality.Percolation.MassRowLowerBounds

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 0

theorem Classical.next_vertex_mass_uniform_lower {rule : Rule} (h : rule.Classical)
    (p lower : ℝ) (hp : 0 < p) (hp' : p < 1) (hlower : 0 ≤ lower) (n : ℕ)
    (hbase : ∀ state, lower ≤ (rule.generation n).network.conditionalVertexMass p state) :
    ∀ state, 2 * lower ≤ (rule.generation (n + 1)).network.conditionalVertexMass p state := by
  have hq := ((rule.generation n).network.reliability_pos_iff_connected hp hp').mpr ((h.generation n).connected _)
  have hq' := (rule.generation n).network.reliability_lt_one hp hp'
  intro state
  rw [h.generation_conditionalVertexMass_offcritical p hp hp']
  have hdegree : (2 : ℝ) ≤ rule.network.sourceIncidentEdges.card := by
    exact_mod_cast rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
  have hrows := hdegree.trans (rule.network.massMatrix_row_sum_ge_incident _ hq hq' (h.connected _) state)
  calc
    _ ≤ (∑ child, rule.network.massMatrix ((rule.generation n).network.reliability p) state child) * lower :=
      mul_le_mul_of_nonneg_right hrows hlower
    _ = ∑ child, rule.network.massMatrix ((rule.generation n).network.reliability p) state child * lower := Finset.sum_mul ..
    _ ≤ ∑ child, rule.network.massMatrix ((rule.generation n).network.reliability p) state child *
        (rule.generation n).network.conditionalVertexMass p child :=
      Finset.sum_le_sum (fun child _ => mul_le_mul_of_nonneg_left (hbase child)
        (rule.network.massMatrix_nonneg hq.le hq'.le state child))
    _ ≤ _ := le_add_of_nonneg_left (rule.network.conditionalInternalMean_nonneg _ hq.le hq'.le _ _ _)

theorem Classical.exit_first_moment_uniform_lower {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ radius lower : ℝ, 0 < radius ∧ 0 < lower ∧
      ∀ p, 0 < p → p < 1 → ∀ n : ℕ,
        (∀ j ≤ n, |rule.network.reliability^[j] p - critical| < radius) → ∀ state,
          lower * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (n + 1) ≤
            (rule.generation (n + 1)).network.conditionalVertexMass p state := by
  obtain ⟨radius, hradius, hb⟩ := h.preexit_moment_bounds critical hc hc' hfixed
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ := hb 1
  have hrho : 0 < (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).2.1)
  refine ⟨radius, 2 * lower / ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal),
    hradius, div_pos (mul_pos (by norm_num) hlower) hrho, ?_⟩
  intro p hp hp' n horbit state
  have hbase (child : LiveState) : lower *
      ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ n ≤
        (rule.generation n).network.conditionalVertexMass p child := by
    simpa only [one_mul, conditionalVertexMoment_one] using (hbounds p hp hp' n horbit child).1
  have hnext := h.next_vertex_mass_uniform_lower p _ hp hp'
    (mul_nonneg hlower.le (pow_nonneg hrho.le n)) n hbase state
  convert hnext using 1
  rw [pow_succ]
  field_simp [hrho.ne']
  <;> ring

end
end Universality.Rule
