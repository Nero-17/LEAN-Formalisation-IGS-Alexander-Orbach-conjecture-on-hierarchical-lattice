import Universality.Percolation.ProbabilityEndpoints
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.IntermediateValue

namespace Universality
noncomputable section
open Filter Set
open scoped Topology

theorem exists_positive_near_zero_of_negative_slope (f : ℝ → ℝ)
    (hf : HasDerivAt f (-1) 0) (hzero : f 0 = 0) :
    ∃ x, 0 < x ∧ x < 1 / 2 ∧ f x < 0 := by
  have hslope : ∀ᶠ x in 𝓝[>] (0 : ℝ), slope f 0 x < 0 :=
    (hf.hasDerivWithinAt (s := Ioi 0)).limsup_slope_le' (by simp) (by norm_num)
  have hsmall : ∀ᶠ x in 𝓝[>] (0 : ℝ), x < 1 / 2 :=
    nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hpositive : ∀ᶠ x in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
  obtain ⟨x, hx, hxsmall, hxslope⟩ := (hpositive.and (hsmall.and hslope)).exists
  refine ⟨x, hx, hxsmall, ?_⟩
  rw [slope_def_field, hzero, sub_zero, sub_zero] at hxslope
  simpa only [zero_mul] using (div_lt_iff₀ hx).mp hxslope

theorem exists_below_one_of_negative_slope (f : ℝ → ℝ)
    (hf : HasDerivAt f (-1) 1) (hone : f 1 = 0) :
    ∃ x, 1 / 2 < x ∧ x < 1 ∧ 0 < f x := by
  have hslope : ∀ᶠ x in 𝓝[<] (1 : ℝ), slope f 1 x < 0 :=
    (hf.hasDerivWithinAt (s := Iio 1)).limsup_slope_le' (by simp) (by norm_num)
  have hlarge : ∀ᶠ x in 𝓝[<] (1 : ℝ), 1 / 2 < x :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hless : ∀ᶠ x in 𝓝[<] (1 : ℝ), x < 1 := self_mem_nhdsWithin
  obtain ⟨x, hxlarge, hx, hxslope⟩ := (hlarge.and (hless.and hslope)).exists
  refine ⟨x, hxlarge, hx, ?_⟩
  rw [slope_def_field, hone, sub_zero] at hxslope
  simpa only [zero_mul] using (div_lt_iff_of_neg (sub_neg.mpr hx)).mp hxslope

namespace FiniteNetwork

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

/-- Existence of a nontrivial finite reliability fixed point. Identifying
this point with an infinite-volume percolation threshold is a separate claim. -/
theorem exists_interior_fixed_point
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target)
    (hcut : ∀ edge, R.crosses (onlyClosed edge) = true) :
    ∃ p : ℝ, 0 < p ∧ p < 1 ∧ R.reliability p = p := by
  have hderiv (p : ℝ) : HasDerivAt (fun p => R.reliability p - p)
      (deriv R.reliability p - 1) p :=
    (R.hasDerivAt_reliability p).differentiableAt.hasDerivAt.sub (hasDerivAt_id p)
  have hzero : HasDerivAt (fun p => R.reliability p - p) (-1) 0 := by
    simpa only [R.derivative_zero_zero hscale, zero_sub] using hderiv 0
  have hone : HasDerivAt (fun p => R.reliability p - p) (-1) 1 := by
    simpa only [R.derivative_one_zero hcut, zero_sub] using hderiv 1
  obtain ⟨a, ha, ha', hfa⟩ := exists_positive_near_zero_of_negative_slope _ hzero
    (by rw [R.reliability_zero]; ring)
  obtain ⟨b, hb, hb', hfb⟩ := exists_below_one_of_negative_slope _ hone
    (by rw [R.reliability_one hconnected]; ring)
  have hab : a ≤ b := le_of_lt (ha'.trans hb)
  have hcontinuous : Continuous (fun p => R.reliability p - p) :=
    continuous_iff_continuousAt.mpr (fun p => (hderiv p).continuousAt)
  obtain ⟨p, hp, heq⟩ := intermediate_value_Icc hab hcontinuous.continuousOn
    ⟨le_of_lt hfa, le_of_lt hfb⟩
  exact ⟨p, ha.trans_le hp.1, hp.2.trans_lt hb', sub_eq_zero.mp heq⟩

end FiniteNetwork
end
end Universality
