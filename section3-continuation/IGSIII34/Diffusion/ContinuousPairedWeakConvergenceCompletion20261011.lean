import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter
open scoped Topology

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def countableContinuousPastTestCompletion20261011 {count : ℕ}
    (test : C(Fin count → Space, ℝ)) (coordinates : Fin count → ℕ) : C(ℕ → Space, ℝ) where
  toFun path := test (fun index => path (coordinates index))
  continuous_toFun := test.continuous.comp (by fun_prop)

theorem countable_paired_integrals_tendsto_completion20261011 {count : ℕ}
    (laws : ℕ → ProbabilityMeasure (ℕ → Space))
    (law : ProbabilityMeasure (ℕ → Space)) (convergence : Tendsto laws atTop (𝓝 law))
    (test : C(Fin count → Space, ℝ)) (coordinates : Fin count → ℕ)
    (function : C(Space, ℝ)) (future : ℕ) :
    Tendsto (fun depth => ∫ path, test (fun index => path (coordinates index)) * function (path future) ∂(laws depth : Measure (ℕ → Space)))
      atTop (𝓝 (∫ path, test (fun index => path (coordinates index)) * function (path future) ∂(law : Measure (ℕ → Space)))) := by
  let paired : C(ℕ → Space, ℝ) :=
    { toFun := fun path => test (fun index => path (coordinates index)) * function (path future)
      continuous_toFun := (test.continuous.comp (by fun_prop)).mul (function.continuous.comp (continuous_apply future)) }
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp convergence)
    (BoundedContinuousFunction.mkOfCompact paired)

theorem probability_weighted_uniform_error_completion20261011
    {Outcome : Type*} [MeasurableSpace Outcome]
    (law : Measure Outcome) [IsProbabilityMeasure law]
    (past residual : Outcome → ℝ) (pastBound errorBound : ℝ)
    (pastBounded : ∀ᵐ outcome ∂law, ‖past outcome‖ ≤ pastBound)
    (pastBoundNonnegative : 0 ≤ pastBound)
    (residualBounded : ∀ᵐ outcome ∂law, ‖residual outcome‖ ≤ errorBound) :
    ‖∫ outcome, past outcome * residual outcome ∂law‖ ≤ pastBound * errorBound := by
  have productBound : ∀ᵐ outcome ∂law, ‖past outcome * residual outcome‖ ≤ pastBound * errorBound := by
    filter_upwards [pastBounded, residualBounded] with outcome pastControl residualControl
    rw [norm_mul]
    exact mul_le_mul pastControl residualControl (norm_nonneg _) pastBoundNonnegative
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const productBound

end
end IGSIII34.Diffusion
