import IGSIII34.Diffusion.ContinuousWalkGeneratorEstimate
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

theorem unitExponential_cdf_slope :
    Tendsto (fun time : ℝ => (1 - Real.exp (-time)) / time) (𝓝[>] 0) (𝓝 1) := by
  have derivative : HasDerivAt (fun time : ℝ => 1 - Real.exp (-time)) 1 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).sub ((hasDerivAt_id (0 : ℝ)).neg.exp) using 1 <;>
      first | rfl | norm_num
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using derivative.tendsto_slope_zero_right

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

/-- The actual constructed continuous walk has the rate-one finite graph
generator as its right derivative at the initial time, for every bounded
potential. This proves an infinitesimal identity, separately from the full
continuous-time Markov property. -/
theorem finiteContinuousWalkSampleLaw_generator_bounded
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) (constant : ℝ) (constantNonnegative : 0 ≤ constant)
    (bound : ∀ vertex, |potential vertex| ≤ constant) :
    Tendsto (fun time : ℝ =>
      ((∫ sample, potential (holdingTimePath sample.1 sample.2 time)
          ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) - potential initial) / time)
      (𝓝[>] 0) (𝓝 (rateOneGenerator endpoint potential initial)) := by
  have cdfZero : Tendsto (fun time : ℝ => 1 - Real.exp (-time)) (𝓝[>] 0) (𝓝 0) := by
    have continuous : ContinuousAt (fun time : ℝ => 1 - Real.exp (-time)) 0 := by fun_prop
    simpa using continuous.tendsto.mono_left nhdsWithin_le_nhds
  have remainderConverges : Tendsto (fun time : ℝ =>
      2 * constant * ((1 - Real.exp (-time)) / time) * (1 - Real.exp (-time)))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using ((unitExponential_cdf_slope.const_mul (2 * constant)).mul cdfZero)
  have residualConverges : Tendsto (fun time : ℝ =>
      ((∫ sample, potential (holdingTimePath sample.1 sample.2 time)
          ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) - potential initial) / time -
        ((1 - Real.exp (-time)) / time) * rateOneGenerator endpoint potential initial)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ remainderConverges
    filter_upwards [self_mem_nhdsWithin] with time timePositive
    have estimate := finiteContinuousWalkSampleLaw_generator_estimate endpoint positiveDegree initial potential
      constant constantNonnegative bound time timePositive.le
    have identity :
        ((∫ sample, potential (holdingTimePath sample.1 sample.2 time)
            ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) - potential initial) / time -
          ((1 - Real.exp (-time)) / time) * rateOneGenerator endpoint potential initial =
        ((∫ sample, potential (holdingTimePath sample.1 sample.2 time)
            ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) -
          (potential initial + (1 - Real.exp (-time)) * rateOneGenerator endpoint potential initial)) / time := by ring
    rw [Real.norm_eq_abs, identity, abs_div]
    rw [show |time| = time from abs_of_pos timePositive]
    calc
      _ ≤ (2 * constant * (1 - Real.exp (-time)) ^ 2) / time :=
        div_le_div_of_nonneg_right estimate timePositive.le
      _ = _ := by ring
  simpa only [sub_add_cancel, zero_add, one_mul] using
    residualConverges.add (unitExponential_cdf_slope.mul_const (rateOneGenerator endpoint potential initial))

theorem finiteContinuousWalkSampleLaw_generator [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) :
    Tendsto (fun time : ℝ =>
      ((∫ sample, potential (holdingTimePath sample.1 sample.2 time)
          ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) - potential initial) / time)
      (𝓝[>] 0) (𝓝 (rateOneGenerator endpoint potential initial)) := by
  apply finiteContinuousWalkSampleLaw_generator_bounded endpoint positiveDegree initial potential
    (∑ vertex, |potential vertex|) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  intro vertex
  exact Finset.single_le_sum (f := fun vertex : Vertex => |potential vertex|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ vertex)

theorem actualFiniteContinuousWalkSampleLaw_generator (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth)
    (potential : ActualFiniteCluster rule configuration scale scalePositive depth → ℝ) :
    Tendsto (fun time : ℝ =>
      ((∫ sample, potential (holdingTimePath sample.1 sample.2 time)
          ∂finiteContinuousWalkSampleLaw
            (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
            (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
            (cluster_degree_positive (rule.generation depth).network (configuration depth) (crossing depth))
            (Measure.dirac initial)) -
        potential initial) / time) (𝓝[>] 0)
      (𝓝 (rateOneGenerator (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
        potential initial)) :=
  finiteContinuousWalkSampleLaw_generator _ _ initial potential

end
end IGSIII34.Diffusion
