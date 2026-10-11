import Universality.Examples.WheatstoneResponseData

namespace Universality
noncomputable section
open Set Filter Polynomial
open scoped Topology

def wheatstoneHalfIteration (p : Icc (1 / 2 : ℝ) 1) : Icc (1 / 2 : ℝ) 1 :=
  ⟨wheatstoneRealCrossing.eval p, wheatstone_real_crossing_maps_half p.property⟩

def wheatstoneHalfCenter : Icc (1 / 2 : ℝ) 1 := ⟨1 / 2, by norm_num⟩

def wheatstoneRealSecant : Polynomial ℝ := 2 * X ^ 4 - 4 * X ^ 3 + 2 * X + 1

theorem wheatstone_real_secant_identity (p : ℝ) :
    wheatstoneRealCrossing.eval p - 1 / 2 = (p - 1 / 2) * wheatstoneRealSecant.eval p := by
  simp [wheatstoneRealCrossing, wheatstoneRealSecant]
  <;> ring

theorem wheatstone_real_secant_pos (p : ℝ) (hp : p ∈ Icc (1 / 2 : ℝ) 1) :
    0 < wheatstoneRealSecant.eval p := by
  have hp0 : 0 ≤ p := by linarith [hp.1]
  have hgap : 0 ≤ 1 - p := sub_nonneg.mpr hp.2
  have hsquare := mul_nonneg hp0 hgap
  have hlast : 0 ≤ 1 + p - p ^ 2 := by nlinarith
  have hproduct := mul_nonneg (mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ 2 by norm_num) hp0) hgap) hlast
  have hid : wheatstoneRealSecant.eval p = 1 + 2 * p * (1 - p) * (1 + p - p ^ 2) := by
    simp [wheatstoneRealSecant]
    <;> ring
  rw [hid]
  linarith

theorem wheatstone_real_secant_half : wheatstoneRealSecant.eval (1 / 2) = (13 / 8 : ℝ) := by
  norm_num [wheatstoneRealSecant]

theorem wheatstone_half_iteration_fixed : wheatstoneHalfIteration wheatstoneHalfCenter = wheatstoneHalfCenter := by
  apply Subtype.ext
  change wheatstoneRealCrossing.eval (1 / 2) = (1 / 2 : ℝ)
  norm_num [wheatstoneRealCrossing]

theorem wheatstone_half_iteration_continuous : Continuous wheatstoneHalfIteration := by
  have hpolynomial : Continuous wheatstoneRealCrossing.eval :=
    continuous_iff_continuousAt.mpr (fun p => (wheatstoneRealCrossing.hasDerivAt p).continuousAt)
  exact (hpolynomial.comp continuous_subtype_val).subtype_mk _

theorem wheatstone_half_iteration_value (p : Icc (1 / 2 : ℝ) 1) (depth : ℕ) :
    ((wheatstoneHalfIteration^[depth] p : Icc (1 / 2 : ℝ) 1) : ℝ) =
      wheatstoneNetwork.reliability^[depth] (p : ℝ) := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change wheatstoneRealCrossing.eval ↑(wheatstoneHalfIteration^[depth] p) = _
      rw [wheatstoneRealCrossing_eval, ih]

theorem wheatstone_half_iteration_escape (p : Icc (1 / 2 : ℝ) 1) (hp : p ≠ wheatstoneHalfCenter) :
    ∃ depth : ℕ, (1 / 4 : ℝ) ≤ dist (wheatstoneHalfIteration^[depth] p) wheatstoneHalfCenter := by
  have hpval : (p : ℝ) ≠ (1 / 2 : ℝ) := fun heq => hp (Subtype.ext heq)
  have hpAbove : (1 / 2 : ℝ) < p := lt_of_le_of_ne p.property.1 hpval.symm
  have hlimit := (wheatstoneNetwork.iterate_reliability_tendsto_one (1 / 2) p
    (by norm_num) (by norm_num) (by norm_num [wheatstone_reliability])
      hpAbove p.property.2 wheatstoneRule_classical.scale).sub_const (1 / 2) |>.abs
  obtain ⟨depth, hdepth⟩ := (hlimit.eventually
    (lt_mem_nhds (show (1 / 4 : ℝ) < |1 - 1 / 2| by norm_num))).exists
  refine ⟨depth, ?_⟩
  simpa only [Subtype.dist_eq, Real.dist_eq, wheatstone_half_iteration_value, wheatstoneHalfCenter]
    using hdepth.le

end
end Universality
