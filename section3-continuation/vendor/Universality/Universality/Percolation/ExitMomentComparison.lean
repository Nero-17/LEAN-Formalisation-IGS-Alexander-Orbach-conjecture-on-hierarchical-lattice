import Universality.Percolation.PreexitMomentBounds
import Universality.Percolation.ConditionalCompactBounds
import Universality.Probability.GradedMomentBounds

namespace Universality.Rule
noncomputable section
open FiniteNetwork
set_option maxHeartbeats 0

/-- The last step into a fixed interior exit interval costs only a uniform
factor per moment degree. The preceding orbit stays in the critical neighborhood. -/
theorem Classical.exit_moment_critical_comparison {rule : Rule} (h : rule.Classical)
    (critical lower upper : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (hupper : upper < 1) :
    ∃ radius factor : ℝ, 0 < radius ∧ 1 ≤ factor ∧
      ∀ p, 0 < p → p < 1 → ∀ n : ℕ,
        (∀ j ≤ n, |rule.network.reliability^[j] p - critical| < radius) →
        lower ≤ rule.network.reliability^[n + 1] p → rule.network.reliability^[n + 1] p ≤ upper →
        ∀ state order,
          (rule.generation (n + 1)).network.conditionalVertexMoment p state order ≤
            factor ^ order * (rule.generation (n + 1)).network.conditionalVertexMoment critical state order := by
  obtain ⟨radius, hradius, hpre⟩ := h.preexit_moment_comparison_with_distortion critical hc hc' hfixed 2 (by norm_num)
  obtain ⟨factor, hfactor, hweight⟩ := rule.network.conditionalCellWeight_compact_comparison
    critical lower upper hc hc' hlower hinterval hupper (h.connected _)
  refine ⟨radius, factor * 2, hradius, by nlinarith, ?_⟩
  intro p hp hp' n horbit hlow hhigh state order
  by_cases hzero : order = 0
  · subst order
    unfold conditionalVertexMoment
    rw [(rule.generation (n + 1)).network.conditionalInternalMoment_zero p
      (((rule.generation (n + 1)).network.reliability_pos_iff_connected hp hp').mpr ((h.generation (n + 1)).connected _))
      ((rule.generation (n + 1)).network.reliability_lt_one hp hp'),
      (rule.generation (n + 1)).network.conditionalInternalMoment_zero critical
      (by rwa [rule.generation_fixed_point critical hfixed (n + 1)])
      (by rwa [rule.generation_fixed_point critical hfixed (n + 1)])]
    simp
  rw [h.generation_conditionalVertexMoment_offcritical p hp hp',
    h.generation_conditionalVertexMoment_offcritical critical hc hc', rule.generation_fixed_point critical hfixed n]
  apply branchingMomentOperator_scale_comparison
    (fun state => rule.network.conditionalCellWeight ((rule.generation n).network.reliability p) (state == .connected))
    (fun state => rule.network.conditionalCellWeight critical (state == .connected))
    (fun state configuration => (rule.network.internalSelectedMass true (state == .both) configuration : ℝ))
    rule.network.childState
    (fun state k => (rule.generation n).network.conditionalVertexMoment p state k)
    (fun state k => (rule.generation n).network.conditionalVertexMoment critical state k)
  · intro state configuration
    exact rule.network.conditionalCellWeight_nonneg
      ((rule.generation n).network.reliability_nonneg hp.le hp'.le)
      ((rule.generation n).network.reliability_le_one hp.le hp'.le) _ _
  · exact fun state configuration => rule.network.conditionalCellWeight_nonneg hc.le hc'.le _ _
  · exact fun state configuration => Nat.cast_nonneg _
  · exact fun state k => (rule.generation n).network.conditionalInternalMoment_nonneg p hp.le hp'.le _ _ _ _
  · exact fun state k => (rule.generation n).network.conditionalInternalMoment_nonneg critical hc.le hc'.le _ _ _ _
  · exact hfactor
  · norm_num
  · intro state configuration
    rw [rule.generation_reliability_iterate]
    exact hweight _ hlow hhigh _ _
  · exact fun state k => (hpre p hp hp' n horbit state k).1
  · omega

/-- A genuine finite-order initial comparison for the whole post-exit
recursion, with uniform constants on a fixed interior exit interval. -/
theorem Classical.exit_moment_initial_bound {rule : Rule} (h : rule.Classical)
    (critical lower upper : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical)
    (hlower : 0 < lower) (hinterval : lower ≤ upper) (hupper : upper < 1) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ order : ℕ, ∃ constant : ℝ, 1 ≤ constant ∧
      ∀ p, 0 < p → p < 1 → ∀ n : ℕ,
        (∀ j ≤ n, |rule.network.reliability^[j] p - critical| < radius) →
        ∀ exitParameter, rule.network.reliability^[n + 1] p = exitParameter →
          lower ≤ exitParameter → exitParameter ≤ upper → ∀ state k, k ≤ order →
          (rule.generation (n + 1)).network.conditionalVertexMoment p state k ≤
            (constant * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (n + 1)) ^ k *
              rule.network.conditionalVertexMoment exitParameter state k := by
  obtain ⟨radius, factor, hradius, hfactor, hcompare⟩ :=
    h.exit_moment_critical_comparison critical lower upper hc hc' hfixed hlower hinterval hupper
  refine ⟨radius, hradius, ?_⟩
  intro order
  have hexists (k : Fin (order + 1)) : ∃ bound : ℝ, 0 < bound ∧ ∀ n state,
      (rule.generation n).network.conditionalVertexMoment critical state k ≤
        bound * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (k.val * n) := by
    obtain ⟨a, b, ha, hb, hab⟩ := h.internal_vertex_moment_comparison critical hc hc' hfixed k
    exact ⟨b, hb, fun n state => (hab n state).2⟩
  choose bound hbound hboundMoment using hexists
  let total : ℝ := 1 + ∑ k : Fin (order + 1), bound k
  let minimum : ℝ := (min lower (1 - upper)) ^ rule.edges
  have htotal : 0 < total := add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun k _ => (hbound k).le))
  have hminimum : 0 < minimum := pow_pos (lt_min hlower (sub_pos.mpr hupper)) _
  have hspectral : 1 ≤ (spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal :=
    ((rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance critical hc hc' hfixed h.massAdmissible.symmetric h.scale).2.1).le
  refine ⟨max 1 (total / minimum) * factor,
    (le_max_left 1 (total / minimum)).trans (le_mul_of_one_le_right (zero_le_one.trans (le_max_left _ _)) hfactor), ?_⟩
  intro p hp hp' n horbit exitParameter hparameter hlow hhigh state k hk
  have hexit : 0 < exitParameter := hlower.trans_le hlow
  have hexit' : exitParameter < 1 := hhigh.trans_lt hupper
  have htop := hcompare p hp hp' n horbit (by rwa [hparameter]) (by rwa [hparameter])
  have hgraded := graded_moment_comparison_of_bounds
    (fun state k => (rule.generation (n + 1)).network.conditionalVertexMoment p state k)
    (rule.network.conditionalVertexMoment exitParameter) order total
    (factor * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (n + 1)) minimum
    htotal.le
    (hfactor.trans (le_mul_of_one_le_right (zero_le_one.trans hfactor) (one_le_pow₀ hspectral))) hminimum
    (fun state => (rule.generation (n + 1)).network.conditionalInternalMoment_zero p
      (((rule.generation (n + 1)).network.reliability_pos_iff_connected hp hp').mpr ((h.generation (n + 1)).connected _))
      ((rule.generation (n + 1)).network.reliability_lt_one hp hp') _ _ _)
    (fun state => rule.network.conditionalInternalMoment_zero exitParameter
      ((rule.network.reliability_pos_iff_connected hexit hexit').mpr (h.connected _))
      (rule.network.reliability_lt_one hexit hexit') _ _ _)
    (by
      intro state j hj
      have hboundTotal : bound ⟨j, by omega⟩ ≤ total := by
        have hs := Finset.single_le_sum (fun i _ => (hbound i).le) (Finset.mem_univ (⟨j, by omega⟩ : Fin (order + 1)))
        dsimp [total]
        linarith
      calc
        _ ≤ factor ^ j * (bound ⟨j, by omega⟩ *
          ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (j * (n + 1))) :=
          (htop state j).trans (mul_le_mul_of_nonneg_left (hboundMoment ⟨j, by omega⟩ (n + 1) state)
            (pow_nonneg (zero_le_one.trans hfactor) _))
        _ ≤ factor ^ j * (total *
          ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (j * (n + 1))) := by gcongr
        _ = _ := by rw [mul_pow, ← pow_mul, Nat.mul_comm (n + 1) j]; ring)
    (fun state j hj => rule.network.conditionalVertexMoment_uniform_lower lower upper exitParameter
      hlower hupper hlow hhigh (h.connected _) h.scale state j)
  simpa only [mul_assoc] using hgraded state k hk

end
end Universality.Rule
