import IGSIII34.Spectral.ComponentResolvent
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-! The compact form-ball embedding step of Appendix B, proved by
Arzelà--Ascoli from the resistance inequality and the form-ball bounds.
It does not assume compact embedding as an input.
-/
set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Set
open scoped BoundedContinuousFunction

theorem resistance_ball_equicontinuous
    {Carrier : Type*} [MetricSpace Carrier]
    (family : Set (Carrier →ᵇ ℝ)) (energy : (Carrier →ᵇ ℝ) → ℝ)
    (energyBound : ∀ function ∈ family, energy function ≤ 1)
    (resistanceBound : ∀ function ∈ family, ∀ first second,
      (function first - function second) ^ 2 ≤ dist first second * energy function) :
    Equicontinuous (fun function : family => (function.val : Carrier → ℝ)) := by
  intro point
  apply Metric.equicontinuousAt_iff.mpr
  intro epsilon positive
  refine ⟨epsilon ^ 2, sq_pos_of_pos positive, ?_⟩
  intro other close function
  have incrementBound := (resistanceBound function.val function.property point other).trans
    (mul_le_mul_of_nonneg_left (energyBound function.val function.property) dist_nonneg)
  rw [mul_one, dist_comm] at incrementBound
  rw [Real.dist_eq]
  have squareIdentity := sq_abs (function.val point - function.val other)
  nlinarith [abs_nonneg (function.val point - function.val other)]

theorem compact_closure_of_resistance_form_ball
    {Carrier : Type*} [MetricSpace Carrier] [CompactSpace Carrier]
    [MeasurableSpace Carrier] [BorelSpace Carrier]
    (measure : Measure Carrier) [IsProbabilityMeasure measure]
    (family : Set (Carrier →ᵇ ℝ)) (energy : (Carrier →ᵇ ℝ) → ℝ) (diameter : ℝ)
    (diameterNonnegative : 0 ≤ diameter)
    (diameterBound : ∀ first second : Carrier, dist first second ≤ diameter)
    (energyNonnegative : ∀ function ∈ family, 0 ≤ energy function)
    (energyBound : ∀ function ∈ family, energy function ≤ 1)
    (squareBound : ∀ function ∈ family, (∫ point, function point ^ 2 ∂measure) ≤ 1)
    (resistanceBound : ∀ function ∈ family, ∀ first second,
      (function first - function second) ^ 2 ≤ dist first second * energy function) :
    IsCompact (closure family) := by
  apply BoundedContinuousFunction.arzela_ascoli (Icc (-(diameter + 2)) (diameter + 2)) isCompact_Icc family
  · intro function point membership
    have integrable : Integrable (fun point => function point ^ 2) measure := by
      apply ((function * function).integrable measure).congr
      exact Filter.Eventually.of_forall (fun point => by
        change function point * function point = function point ^ 2
        ring)
    have evaluated := point_evaluation_le_of_resistance_inequality measure function point diameter
      (energy function) (by simp [measureReal_def]) integrable
      (Filter.Eventually.of_forall (fun other =>
        (resistanceBound function membership point other).trans
          (mul_le_mul_of_nonneg_right (diameterBound point other) (energyNonnegative function membership))))
    have mass : measure.real univ = 1 := by simp [measureReal_def]
    rw [mass] at evaluated
    have energyProduct := mul_le_mul_of_nonneg_left (energyBound function membership) diameterNonnegative
    have boundedSquare : function point ^ 2 ≤ 2 + 2 * diameter := by
      have integralBound := squareBound function membership
      norm_num at evaluated
      nlinarith
    have absoluteBound : |function point| ≤ diameter + 2 := by
      nlinarith [sq_abs (function point), abs_nonneg (function point), sq_nonneg diameter]
    exact abs_le.mp absoluteBound
  · exact resistance_ball_equicontinuous family energy energyBound resistanceBound

end
end IGSIII34.Spectral
