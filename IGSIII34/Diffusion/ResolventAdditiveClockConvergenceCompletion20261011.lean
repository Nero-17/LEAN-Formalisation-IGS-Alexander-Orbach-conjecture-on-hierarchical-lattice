import IGSIII34.Diffusion.ResolventAdditiveClockCompletion20261011
import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4400000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped _root_.Topology BigOperators NNReal ENNReal

def finitePotentialUniformSizeCompletion20261011 {Vertex : Type*} [Fintype Vertex] [Nonempty Vertex]
    (potential : Vertex → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun vertex => |potential vertex|)

theorem finitePotentialUniformSize_nonnegative_completion20261011
    {Vertex : Type*} [Fintype Vertex] [Nonempty Vertex] (potential : Vertex → ℝ) :
    0 ≤ finitePotentialUniformSizeCompletion20261011 potential := by
  classical
  exact (abs_nonneg (potential (Classical.choice (inferInstance : Nonempty Vertex)))).trans
    (Finset.le_sup' (f := fun vertex => |potential vertex|) (Finset.mem_univ _))

theorem finitePotentialUniformSize_bound_completion20261011
    {Vertex : Type*} [Fintype Vertex] [Nonempty Vertex] (potential : Vertex → ℝ) (vertex : Vertex) :
    |potential vertex| ≤ finitePotentialUniformSizeCompletion20261011 potential :=
  Finset.le_sup' (f := fun vertex => |potential vertex|) (Finset.mem_univ vertex)

/-- Uniformly vanishing true resolvent correctors force the original
walk's additive functional to vanish simultaneously at every prefix on
each fixed clock-scaled interval, for arbitrary initial distributions.
The probability estimate is proved from the actual maximal martingale
bound; no small-prefix probability is an input. -/
theorem finiteGraphResolvent_additive_prefix_probability_tendsto_completion20261011
    (Vertices Edges : ℕ → Type*)
    [∀ index, Fintype (Vertices index)] [∀ index, DecidableEq (Vertices index)]
    [∀ index, MeasurableSpace (Vertices index)] [∀ index, MeasurableSingletonClass (Vertices index)]
    [∀ index, StandardBorelSpace (Vertices index)] [∀ index, Nonempty (Vertices index)]
    [∀ index, Fintype (Edges index)]
    (endpoint : ∀ index, Edges index → Vertices index × Vertices index)
    (positiveDegree : ∀ index vertex, 0 < degree (endpoint index) vertex)
    (initial : ∀ index, ProbabilityMeasure (Vertices index))
    (parameter : ℝ) (parameterPositive : 0 < parameter)
    (clocks : ℕ → ℝ) (clocksPositive : ∀ index, 0 < clocks index)
    (forcing : ∀ index, Vertices index → ℝ) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (forcingBound : ∀ index vertex, |forcing index vertex| ≤ bound)
    (correctorsVanish : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ index in atTop, ∀ vertex,
      |finiteGraphResolvent (endpoint index) (positiveDegree index) parameter (clocks index)
        parameterPositive (clocksPositive index).le (forcing index) vertex| < tolerance)
    (horizon radius : ℝ) (horizonNonnegative : 0 ≤ horizon) (radiusPositive : 0 < radius) :
    Tendsto (fun index =>
      (finiteDiscreteWalkLaw (endpoint index) (positiveDegree index) (initial index : Measure (Vertices index))).real
        {path | ∃ prefixLength ≤ ⌊clocks index * horizon⌋₊,
          radius ≤ |finiteWalkScaledAdditiveCompletion20261011 (clocks index) (forcing index) prefixLength path|})
      atTop (𝓝 0) := by
  let potentials : ∀ index, Vertices index → ℝ := fun index =>
    finiteGraphResolvent (endpoint index) (positiveDegree index) parameter (clocks index)
      parameterPositive (clocksPositive index).le (forcing index)
  let sizes : ℕ → ℝ := fun index => finitePotentialUniformSizeCompletion20261011 (potentials index)
  have sizesNonnegative (index : ℕ) : 0 ≤ sizes index := finitePotentialUniformSize_nonnegative_completion20261011 _
  have sizesBound (index : ℕ) (vertex : Vertices index) : |potentials index vertex| ≤ sizes index :=
    finitePotentialUniformSize_bound_completion20261011 _ vertex
  have sizesVanish : Tendsto sizes atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro tolerance positive
    filter_upwards [correctorsVanish tolerance positive] with index small
    have supremumSmall : sizes index < tolerance :=
      (Finset.sup'_lt_iff Finset.univ_nonempty).mpr (fun vertex _ => small vertex)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (sizesNonnegative index)]
    exact supremumSmall
  have driftVanish : Tendsto (fun index => (parameter*horizon+2)*sizes index) atTop (𝓝 0) := by
    simpa only [mul_zero] using sizesVanish.const_mul (parameter*horizon+2)
  have driftSmall : ∀ᶠ index in atTop, (parameter*horizon+2)*sizes index ≤ radius/2 :=
    (driftVanish.eventually (gt_mem_nhds (by positivity : 0 < radius/2))).mono (fun _ bound => bound.le)
  let probabilities : ℕ → ℝ := fun index =>
    (finiteDiscreteWalkLaw (endpoint index) (positiveDegree index) (initial index : Measure (Vertices index))).real
      {path | ∃ prefixLength ≤ ⌊clocks index*horizon⌋₊,
        radius ≤ |finiteWalkScaledAdditiveCompletion20261011 (clocks index) (forcing index) prefixLength path|}
  have denominatorPositive : 0 < (radius/2)^2 := sq_pos_of_pos (by positivity)
  have estimate : ∀ᶠ index in atTop, probabilities index ≤
      (sizes index^2+4*horizon*sizes index*bound)/(radius/2)^2 := by
    filter_upwards [driftSmall] with index small
    have maximal := finiteGraphResolvent_additive_maximal_bound_completion20261011
      (endpoint index) (positiveDegree index) (initial index : Measure (Vertices index))
      parameter (clocks index) parameterPositive (clocksPositive index) (forcing index)
      bound (sizes index) horizon radius boundNonnegative (sizesNonnegative index) horizonNonnegative radiusPositive
      (forcingBound index) (sizesBound index) ⌊clocks index*horizon⌋₊
      (Nat.floor_le (mul_nonneg (clocksPositive index).le horizonNonnegative)) small
    have numeratorNonnegative : 0 ≤ sizes index^2+4*horizon*sizes index*bound := by
      have nonnegative := sizesNonnegative index
      positivity
    have realBound := ENNReal.toReal_mono ENNReal.ofReal_ne_top maximal
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal denominatorPositive.le,
      ENNReal.toReal_ofReal numeratorNonnegative] at realBound
    have normalizedBound : (radius/2)^2 * probabilities index ≤
        sizes index^2+4*horizon*sizes index*bound := by
      convert realBound using 1 <;> rfl
    exact (le_div_iff₀ denominatorPositive).mpr (by simpa only [mul_comm] using normalizedBound)
  have numeratorVanish : Tendsto (fun index => sizes index^2+4*horizon*sizes index*bound) atTop (𝓝 0) := by
    simpa only [zero_pow (by omega : (2:ℕ) ≠ 0), mul_zero, zero_mul, add_zero] using
      (sizesVanish.pow 2).add ((sizesVanish.const_mul (4*horizon)).mul_const bound)
  have quotientVanish : Tendsto (fun index => (sizes index^2+4*horizon*sizes index*bound)/(radius/2)^2) atTop (𝓝 0) := by
    simpa only [zero_div] using numeratorVanish.div_const ((radius/2)^2)
  exact squeeze_zero' (Eventually.of_forall (fun index => measureReal_nonneg)) estimate quotientVanish

end
end IGSIII34.Diffusion
