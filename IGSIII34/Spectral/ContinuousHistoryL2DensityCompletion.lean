import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space

/-! Continuous past tests determine every bounded measurable scalar
conditional moment on a compact history space, via real L2 density. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Filter InnerProductSpace
open scoped Topology

variable {History : Type*} [MetricSpace History] [CompactSpace History]
  [MeasurableSpace History] [BorelSpace History]
  (law : Measure History) [IsFiniteMeasure law] [law.WeaklyRegular]

theorem bounded_measurable_eq_zero_of_continuous_tests_completion
    (function : History → ℝ) (functionMeasurable : AEStronglyMeasurable function law)
    (bound : ℝ) (bounded : ∀ᵐ retained ∂law, ‖function retained‖ ≤ bound)
    (tests : ∀ test : C(History, ℝ), (∫ retained, function retained * test retained ∂law) = 0) :
    function =ᵐ[law] 0 := by
  have squareIntegrable : MemLp function 2 law := MemLp.of_bound functionMeasurable bound bounded
  have testOrthogonal : ∀ test : C(History, ℝ),
      ⟪squareIntegrable.toLp function, ContinuousMap.toLp 2 law ℝ test⟫_ℝ = 0 := by
    intro test
    rw [L2.inner_def]
    have integralSame : (∫ retained,
      ⟪(squareIntegrable.toLp function) retained, (ContinuousMap.toLp 2 law ℝ test) retained⟫_ℝ ∂law) =
      ∫ retained, function retained * test retained ∂law := by
      apply integral_congr_ae
      filter_upwards [squareIntegrable.coeFn_toLp, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) law test]
        with retained functionSame testSame
      rw [functionSame, testSame, Real.inner_apply]
    rw [integralSame, tests test]
  have allOrthogonal : (fun value : Lp ℝ 2 law => ⟪squareIntegrable.toLp function, value⟫_ℝ) = (fun _ => 0) :=
    (ContinuousMap.toLp_denseRange ℝ law ℝ (p := 2) (by norm_num)).equalizer
      (innerSL ℝ (squareIntegrable.toLp function)).continuous continuous_const (funext testOrthogonal)
  have lpZero : squareIntegrable.toLp function = 0 :=
    inner_self_eq_zero.mp (congrFun allOrthogonal (squareIntegrable.toLp function))
  have representative := squareIntegrable.coeFn_toLp
  rw [lpZero] at representative
  exact representative.symm.trans (Lp.coeFn_zero _ _ _)

end
end IGSIII34.Spectral
