import Universality.Analysis.ZeroDerivativeIteration
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar small-ball recursions

These analytic lemmas turn a thinning map and its small-ball recursion into
convergence and weighted summability.  They do not identify a graph probability
with a scalar map, and they do not assume an inverse-moment conclusion.
The finite-graph probability bridge and the integral bridge are separate.
-/

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open Filter
open scoped Topology

theorem fixed_point_eq_zero {map : ℝ → ℝ} {atom : ℝ}
    (nonnegative : 0 ≤ atom) (notAll : atom < 1)
    (strict : ∀ value, 0 < value → value < 1 → map value < value)
    (fixed : map atom = atom) : atom = 0 := by
  by_contra nonzero
  have positive : 0 < atom := lt_of_le_of_ne nonnegative (Ne.symm nonzero)
  have impossible := strict atom positive notAll
  rw [fixed] at impossible
  exact lt_irrefl atom impossible

theorem map_le_self {map : ℝ → ℝ}
    (zero : map 0 = 0)
    (strict : ∀ value, 0 < value → value < 1 → map value < value)
    {value : ℝ} (nonnegative : 0 ≤ value) (belowOne : value < 1) :
    map value ≤ value := by
  rcases nonnegative.eq_or_lt with equality | positive
  · subst value
    exact zero.le
  · exact (strict value positive belowOne).le

theorem iterate_bounds {map : ℝ → ℝ} {start : ℝ}
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (zero : map 0 = 0)
    (nonnegative : ∀ value, 0 ≤ value → value < 1 → 0 ≤ map value)
    (strict : ∀ value, 0 < value → value < 1 → map value < value) :
    ∀ depth : ℕ, 0 ≤ map^[depth] start ∧ map^[depth] start ≤ start := by
  intro depth
  induction depth with
  | zero => exact ⟨startNonnegative, le_rfl⟩
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply']
    exact ⟨nonnegative _ inductionHypothesis.1
        (inductionHypothesis.2.trans_lt startBelowOne),
      (map_le_self zero strict inductionHypothesis.1
        (inductionHypothesis.2.trans_lt startBelowOne)).trans inductionHypothesis.2⟩

theorem iterate_tendsto_zero {map : ℝ → ℝ} {start : ℝ}
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (zero : map 0 = 0)
    (nonnegative : ∀ value, 0 ≤ value → value < 1 → 0 ≤ map value)
    (strict : ∀ value, 0 < value → value < 1 → map value < value)
    (continuous : Continuous map) :
    Tendsto (fun depth : ℕ => map^[depth] start) atTop (𝓝 0) := by
  have bounds := iterate_bounds startNonnegative startBelowOne zero nonnegative strict
  have decreasing : Antitone (fun depth : ℕ => map^[depth] start) := by
    apply antitone_nat_of_succ_le
    intro depth
    rw [Function.iterate_succ_apply']
    exact map_le_self zero strict (bounds depth).1
      ((bounds depth).2.trans_lt startBelowOne)
  have bounded : BddBelow (Set.range (fun depth : ℕ => map^[depth] start)) :=
    ⟨0, by rintro _ ⟨depth, rfl⟩; exact (bounds depth).1⟩
  have convergence := tendsto_atTop_ciInf decreasing bounded
  have limitNonnegative : 0 ≤ ⨅ depth : ℕ, map^[depth] start :=
    le_ciInf (fun depth => (bounds depth).1)
  have limitUpperBound : (⨅ depth : ℕ, map^[depth] start) ≤ start :=
    ciInf_le bounded 0
  have limitFixed := isFixedPt_of_tendsto_iterate convergence continuous.continuousAt
  have limitZero := fixed_point_eq_zero limitNonnegative
    (limitUpperBound.trans_lt startBelowOne) strict limitFixed
  rwa [limitZero] at convergence

/-- Each application of the tail recursion costs one iterate of the thinning map. -/
theorem tail_le_iterate {map : ℝ → ℝ} {tail : ℕ → ℝ} {start : ℝ}
    (monotone : Monotone map) (initial : tail 0 ≤ start)
    (step : ∀ depth, tail (depth + 1) ≤ map (tail depth)) :
    ∀ depth, tail depth ≤ map^[depth] start := by
  intro depth
  induction depth with
  | zero => exact initial
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply']
    exact (step depth).trans (monotone inductionHypothesis)

/-- This is the triangular recursion used for the laws at finite depth. -/
theorem finite_depth_tail_le_iterate {map : ℝ → ℝ} {tail : ℕ → ℕ → ℝ} {start : ℝ}
    (monotone : Monotone map) (initial : ∀ depth, tail depth 0 ≤ start)
    (step : ∀ depth scale, tail (depth + 1) (scale + 1) ≤ map (tail depth scale)) :
    ∀ scale depth, tail (depth + scale) scale ≤ map^[scale] start := by
  intro scale
  induction scale with
  | zero => intro depth; exact initial depth
  | succ scale inductionHypothesis =>
    intro depth
    rw [Nat.add_succ, Function.iterate_succ_apply']
    exact (step (depth + scale) scale).trans (monotone (inductionHypothesis depth))

/-- Domain-restricted version: a reliability polynomial need only be monotone
on the probability interval, not on the whole real line. -/
theorem tail_le_iterate_on {map : ℝ → ℝ} {domain : Set ℝ}
    {tail : ℕ → ℝ} {start : ℝ}
    (monotone : MonotoneOn map domain)
    (orbitWithin : ∀ depth, map^[depth] start ∈ domain)
    (tailWithin : ∀ depth, tail depth ∈ domain)
    (initial : tail 0 ≤ start)
    (step : ∀ depth, tail (depth + 1) ≤ map (tail depth)) :
    ∀ depth, tail depth ≤ map^[depth] start := by
  intro depth
  induction depth with
  | zero => exact initial
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply']
    exact (step depth).trans
      (monotone (tailWithin depth) (orbitWithin depth) inductionHypothesis)

theorem finite_depth_tail_le_iterate_on {map : ℝ → ℝ} {domain : Set ℝ}
    {tail : ℕ → ℕ → ℝ} {start : ℝ}
    (monotone : MonotoneOn map domain)
    (orbitWithin : ∀ depth, map^[depth] start ∈ domain)
    (tailWithin : ∀ depth scale, tail depth scale ∈ domain)
    (initial : ∀ depth, tail depth 0 ≤ start)
    (step : ∀ depth scale, tail (depth + 1) (scale + 1) ≤ map (tail depth scale)) :
    ∀ scale depth, tail (depth + scale) scale ≤ map^[scale] start := by
  intro scale
  induction scale with
  | zero => intro depth; exact initial depth
  | succ scale inductionHypothesis =>
    intro depth
    rw [Nat.add_succ, Function.iterate_succ_apply']
    exact (step (depth + scale) scale).trans
      (monotone (tailWithin (depth + scale) scale) (orbitWithin scale)
        (inductionHypothesis depth))

/-- A triangular finite-depth recursion becomes a uniform bound once shallow
levels have no event.  The latter condition must come from a deterministic
lower bound for the finite-depth variables. -/
theorem uniform_finite_depth_tail_le_iterate_on {map : ℝ → ℝ} {domain : Set ℝ}
    {tail : ℕ → ℕ → ℝ} {start : ℝ}
    (monotone : MonotoneOn map domain)
    (orbitWithin : ∀ depth, map^[depth] start ∈ domain)
    (orbitNonnegative : ∀ depth, 0 ≤ map^[depth] start)
    (tailWithin : ∀ depth scale, tail depth scale ∈ domain)
    (initial : ∀ depth, tail depth 0 ≤ start)
    (step : ∀ depth scale, tail (depth + 1) (scale + 1) ≤ map (tail depth scale))
    (shallowZero : ∀ depth scale, depth < scale → tail depth scale = 0) :
    ∀ depth scale, tail depth scale ≤ map^[scale] start := by
  intro depth scale
  by_cases shallow : depth < scale
  · rw [shallowZero depth scale shallow]
    exact orbitNonnegative scale
  · have bound := finite_depth_tail_le_iterate_on monotone orbitWithin tailWithin initial step
      scale (depth - scale)
    simpa only [Nat.sub_add_cancel (Nat.le_of_not_gt shallow)] using bound

/-- A power recursion yields a doubly exponential bound after scaling by its
constant.  No smallness assumption is needed for this algebraic bound. -/
theorem scaled_power_tail_bound {tail : ℕ → ℝ} {constant : ℝ} {power : ℕ}
    (constantAtLeastOne : 1 ≤ constant) (powerAtLeastTwo : 2 ≤ power)
    (nonnegative : ∀ depth, 0 ≤ tail depth)
    (step : ∀ depth, tail (depth + 1) ≤ constant * tail depth ^ power) :
    ∀ depth, constant * tail depth ≤ (constant * tail 0) ^ (power ^ depth) := by
  intro depth
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
    have constantNonnegative : 0 ≤ constant := le_trans zero_le_one constantAtLeastOne
    have constantPower : constant ^ 2 ≤ constant ^ power :=
      pow_le_pow_right₀ constantAtLeastOne powerAtLeastTwo
    calc
      constant * tail (depth + 1) ≤
          constant * (constant * tail depth ^ power) :=
        mul_le_mul_of_nonneg_left (step depth) constantNonnegative
      _ = constant ^ 2 * tail depth ^ power := by ring
      _ ≤ constant ^ power * tail depth ^ power :=
        mul_le_mul_of_nonneg_right constantPower (pow_nonneg (nonnegative depth) _)
      _ = (constant * tail depth) ^ power := (mul_pow _ _ _).symm
      _ ≤ ((constant * tail 0) ^ (power ^ depth)) ^ power :=
        pow_le_pow_left₀ (mul_nonneg constantNonnegative (nonnegative depth))
          inductionHypothesis power
      _ = (constant * tail 0) ^ (power ^ (depth + 1)) := by
        rw [← pow_mul, pow_succ]

/-- A zero derivative at the attracting fixed point gives summability even
after multiplication by an arbitrary positive geometric weight. -/
theorem weighted_iterate_summable {map : ℝ → ℝ} {start growth : ℝ}
    (startNonnegative : 0 ≤ start) (startBelowOne : start < 1)
    (zero : map 0 = 0)
    (nonnegative : ∀ value, 0 ≤ value → value < 1 → 0 ≤ map value)
    (strict : ∀ value, 0 < value → value < 1 → map value < value)
    (continuous : Continuous map) (derivative : HasDerivAt map 0 0)
    (growthPositive : 0 < growth) :
    Summable (fun depth : ℕ => growth ^ depth * map^[depth] start) := by
  simpa only [sub_zero] using
    Universality.summable_weighted_iterate_sub_of_derivative_zero map start 0 growth
      growthPositive zero derivative
      (iterate_tendsto_zero startNonnegative startBelowOne zero nonnegative strict continuous)

end IGSIII.Chemical.SmallBall
