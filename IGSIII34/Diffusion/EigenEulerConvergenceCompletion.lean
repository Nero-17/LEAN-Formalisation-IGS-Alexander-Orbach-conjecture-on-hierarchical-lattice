import IGSIII34.Diffusion.EigenEulerLimitCompletion

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace IGSIII34.Diffusion
noncomputable section
open Filter
open scoped Topology

theorem eigenEuler_floor_time_tendsto_completion
    (scales : ℕ → ℝ) (positive : ∀ depth, 0 < scales depth)
    (diverges : Tendsto scales atTop atTop) (time : ℝ) (nonnegative : 0 ≤ time) :
    Tendsto (fun depth => (⌊scales depth * time⌋₊ : ℝ) / scales depth) atTop (𝓝 time) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa only [sub_zero] using (tendsto_const_nhds (x := time)).sub (diverges.const_div_atTop 1))
    tendsto_const_nhds
  · apply Eventually.of_forall
    intro depth
    rw [le_div_iff₀ (positive depth)]
    have lower := Nat.lt_floor_add_one (scales depth * time)
    have cancellation : (1 / scales depth) * scales depth = 1 := by field_simp [(positive depth).ne']
    nlinarith
  · apply Eventually.of_forall
    intro depth
    rw [div_le_iff₀ (positive depth)]
    simpa only [mul_comm time] using Nat.floor_le (mul_nonneg (positive depth).le nonnegative)

theorem eigenEuler_shifted_floor_time_tendsto_completion
    (scales : ℕ → ℝ) (positive : ∀ depth, 0 < scales depth)
    (diverges : Tendsto scales atTop atTop)
    (start duration : ℝ) (startNonnegative : 0 ≤ start) (durationNonnegative : 0 ≤ duration) :
    Tendsto (fun depth =>
      ((⌊scales depth * (start + duration)⌋₊ - ⌊scales depth * start⌋₊ : ℕ) : ℝ) / scales depth)
      atTop (𝓝 duration) := by
  have limit := (eigenEuler_floor_time_tendsto_completion scales positive diverges
    (start + duration) (add_nonneg startNonnegative durationNonnegative)).sub
    (eigenEuler_floor_time_tendsto_completion scales positive diverges start startNonnegative)
  apply Tendsto.congr' _ (by simpa only [add_sub_cancel_left] using limit)
  apply Eventually.of_forall
  intro depth
  have ordered : ⌊scales depth * start⌋₊ ≤ ⌊scales depth * (start + duration)⌋₊ :=
    Nat.floor_mono (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right durationNonnegative) (positive depth).le)
  change (⌊scales depth * (start + duration)⌋₊ : ℝ) / scales depth -
    (⌊scales depth * start⌋₊ : ℝ) / scales depth =
    ((⌊scales depth * (start + duration)⌋₊ - ⌊scales depth * start⌋₊ : ℕ) : ℝ) / scales depth
  rw [Nat.cast_sub ordered, sub_div]

theorem eigenEuler_approximate_recursion_tendsto_completion
    (scales : ℕ → ℝ) (scalePositive : ∀ depth, 0 < scales depth)
    (diverges : Tendsto scales atTop atTop)
    (steps : ℕ → ℕ) (time : ℝ)
    (timeLimit : Tendsto (fun depth => (steps depth : ℝ) / scales depth) atTop (𝓝 time))
    (eigenvalue : ℝ) (eigenvalueNonnegative : 0 ≤ eigenvalue)
    (values : ℕ → ℕ → ℝ) (initial : ℝ)
    (initialLimit : Tendsto (fun depth => values depth 0) atTop (𝓝 initial))
    (errors : ℕ → ℝ) (errorNonnegative : ∀ depth, 0 ≤ errors depth)
    (errorLimit : Tendsto errors atTop (𝓝 0))
    (recursion : ∀ depth step,
      |values depth (step + 1) - (1 - eigenvalue / scales depth) * values depth step| ≤ errors depth / scales depth) :
    Tendsto (fun depth => values depth (steps depth)) atTop (𝓝 (Real.exp (-eigenvalue * time) * initial)) := by
  have geometric := (eigenEuler_geometric_tendsto_completion scales diverges steps time timeLimit eigenvalue eigenvalueNonnegative).mul initialLimit
  have errorsVanish : Tendsto (fun depth => (steps depth : ℝ) * (errors depth / scales depth)) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (errorLimit.mul timeLimit).congr (fun depth => by ring)
  have absoluteVanish : Tendsto
      (fun depth => |values depth (steps depth) - (1 - eigenvalue / scales depth) ^ steps depth * values depth 0|)
      atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _ errorsVanish
    filter_upwards [diverges.eventually (eventually_ge_atTop eigenvalue)] with depth large
    exact eigenEuler_discrete_error_completion (values depth) (1 - eigenvalue / scales depth)
      (errors depth / scales depth)
      (sub_nonneg.mpr ((div_le_one (scalePositive depth)).mpr large))
      (sub_le_self _ (div_nonneg eigenvalueNonnegative (scalePositive depth).le))
      (div_nonneg (errorNonnegative depth) (scalePositive depth).le) (recursion depth) (steps depth)
  have differenceVanish : Tendsto
      (fun depth => values depth (steps depth) - (1 - eigenvalue / scales depth) ^ steps depth * values depth 0)
      atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [Real.norm_eq_abs] using absoluteVanish
  simpa only [sub_add_cancel, zero_add] using differenceVanish.add geometric

end
end IGSIII34.Diffusion
