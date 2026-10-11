import IGSIII34.Diffusion.GreedyExitTimesCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem increasing_times_short_gap_count_completion20261011
    (times : ℕ → ℕ) (ordered : Monotone times) (steps horizon window : ℕ)
    (before : times steps ≤ horizon) :
    (steps : ℝ) * window - horizon ≤ (window : ℝ) *
      ∑ step ∈ Finset.range steps,
        (if times (step + 1) ≤ horizon ∧ times (step + 1) ≤ times step + window then (1 : ℝ) else 0) := by
  classical
  have individual (step : ℕ) (member : step ∈ Finset.range steps) :
      (window : ℝ) ≤ ((times (step + 1) : ℝ) - times step) + window *
        (if times (step + 1) ≤ horizon ∧ times (step + 1) ≤ times step + window then (1 : ℝ) else 0) := by
    have bounded := (ordered (show step + 1 ≤ steps by simpa using Finset.mem_range.mp member)).trans before
    have increasing := ordered (Nat.le_succ step)
    by_cases short : times (step + 1) ≤ times step + window
    · rw [if_pos ⟨bounded, short⟩]
      have realIncreasing : (times step : ℝ) ≤ times (step + 1) := by exact_mod_cast increasing
      linarith
    · rw [if_neg (fun both => short both.2)]
      have long : times step + window ≤ times (step + 1) := by omega
      have realLong : (times step : ℝ) + window ≤ times (step + 1) := by exact_mod_cast long
      linarith
  have summed := Finset.sum_le_sum individual
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at summed
  rw [Finset.sum_range_sub (fun step => (times step : ℝ)) steps] at summed
  have lastBound : (times steps : ℝ) ≤ horizon := by exact_mod_cast before
  have startNonnegative : (0 : ℝ) ≤ times 0 := Nat.cast_nonneg _
  linarith

theorem probability_event_from_finite_count_completion20261011
    {Path : Type*} [MeasurableSpace Path] (law : Measure Path) [IsProbabilityMeasure law]
    (event : Set Path) (eventMeasurable : MeasurableSet event)
    (short : ℕ → Set Path) (shortMeasurable : ∀ step, MeasurableSet (short step))
    (steps : ℕ) (coefficient multiplier bound : ℝ) (multiplierNonnegative : 0 ≤ multiplier)
    (onEvent : ∀ path ∈ event, coefficient ≤ multiplier *
      ∑ step ∈ Finset.range steps, (short step).indicator (fun _ => (1 : ℝ)) path)
    (shortBound : ∀ step < steps, law.real (short step) ≤ bound) :
    coefficient * law.real event ≤ multiplier * steps * bound := by
  classical
  have individualIntegrable (step : ℕ) : Integrable ((short step).indicator (fun _ => (1 : ℝ))) law :=
    (integrable_const _).indicator (shortMeasurable step)
  have countIntegrable := integrable_finsetSum (Finset.range steps) (fun step _ => individualIntegrable step)
  have countNonnegative (path : Path) :
      0 ≤ ∑ step ∈ Finset.range steps, (short step).indicator (fun _ => (1 : ℝ)) path :=
    Finset.sum_nonneg (fun step _ => Set.indicator_nonneg (fun _ _ => zero_le_one) path)
  have lower := setIntegral_ge_of_const_le_real eventMeasurable (measure_ne_top law event)
    onEvent (countIntegrable.const_mul multiplier).integrableOn
  have enlarge := setIntegral_mono_set (μ := law) (s := event) (t := Set.univ)
    (f := fun path => multiplier * ∑ step ∈ Finset.range steps,
      (short step).indicator (fun _ => (1 : ℝ)) path)
    (countIntegrable.const_mul multiplier).integrableOn
    (Eventually.of_forall fun path => mul_nonneg multiplierNonnegative (countNonnegative path))
    (Eventually.of_forall fun path _ => Set.mem_univ path)
  have total : (∫ path, multiplier * ∑ step ∈ Finset.range steps,
      (short step).indicator (fun _ => (1 : ℝ)) path ∂law) =
      multiplier * ∑ step ∈ Finset.range steps, law.real (short step) := by
    rw [integral_const_mul, integral_finsetSum]
    · congr 1
      exact Finset.sum_congr rfl (fun step _ => integral_indicator_one (shortMeasurable step))
    · exact fun step _ => individualIntegrable step
  simp only [Measure.restrict_univ] at enlarge
  rw [total] at enlarge
  have sumBound : (∑ step ∈ Finset.range steps, law.real (short step)) ≤ steps * bound := by
    calc
      _ ≤ ∑ _step ∈ Finset.range steps, bound := Finset.sum_le_sum
        (fun step member => shortBound step (Finset.mem_range.mp member))
      _ = _ := by simp
  exact (lower.trans enlarge).trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left sumBound multiplierNonnegative)

theorem probability_first_short_gap_union_completion20261011
    {Path : Type*} [MeasurableSpace Path] (law : Measure Path) [IsProbabilityMeasure law]
    (short : ℕ → Set Path) (steps : ℕ) (bound : ℝ)
    (shortBound : ∀ step < steps, law.real (short step) ≤ bound) :
    law.real (⋃ step : Fin steps, short step) ≤ steps * bound := by
  calc
    _ ≤ ∑ step : Fin steps, law.real (short step) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _step : Fin steps, bound := Finset.sum_le_sum fun step _ => shortBound step step.isLt
    _ = _ := by simp

end
end IGSIII34.Diffusion
