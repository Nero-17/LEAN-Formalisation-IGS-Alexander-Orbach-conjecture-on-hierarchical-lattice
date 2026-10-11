import IGSIII34.Diffusion.VariableSpeedGeneratorEstimate
import IGSIII34.Diffusion.ContinuousWalkGenerator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

theorem exponential_cdf_rate_slope (rate : ℝ) :
    Tendsto (fun time : ℝ => (1 - Real.exp (-(rate * time))) / time) (𝓝[>] 0) (𝓝 rate) := by
  have derivative : HasDerivAt (fun time : ℝ => 1 - Real.exp (-(rate * time))) rate 0 := by
    convert (hasDerivAt_const 0 (1 : ℝ)).sub (((hasDerivAt_id (0 : ℝ)).const_mul rate).neg.exp)
      using 1 <;> first | rfl | simp
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using derivative.tendsto_slope_zero_right

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

/-- The initial infinitesimal generator of the constructed degree-rate walk
is the graph Laplacian, hence rate one along each incident edge. -/
theorem finiteVariableSpeedWalkSampleLaw_generator_bounded
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) (constant : ℝ) (constantNonnegative : 0 ≤ constant)
    (bound : ∀ vertex, |potential vertex| ≤ constant)
    (maximumRate : ℝ) (maximumRateNonnegative : 0 ≤ maximumRate)
    (degreeBound : ∀ vertex, degree endpoint vertex ≤ maximumRate) :
    Tendsto (fun time : ℝ =>
      ((∫ sample, potential (holdingTimePath sample.1
          (variableSpeedHoldingTimes (degree endpoint) sample) time)
          ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) - potential initial) / time)
      (𝓝[>] 0) (𝓝 (laplacian endpoint potential initial)) := by
  have cdfZero : Tendsto (fun time : ℝ => 1 - Real.exp (-(maximumRate * time))) (𝓝[>] 0) (𝓝 0) := by
    have continuous : ContinuousAt (fun time : ℝ => 1 - Real.exp (-(maximumRate * time))) 0 := by fun_prop
    simpa using continuous.tendsto.mono_left nhdsWithin_le_nhds
  have remainderConverges : Tendsto (fun time : ℝ =>
      2 * constant * ((1 - Real.exp (-(maximumRate * time))) / time) *
        (1 - Real.exp (-(maximumRate * time)))) (𝓝[>] 0) (𝓝 0) := by
    simpa using (((exponential_cdf_rate_slope maximumRate).const_mul (2 * constant)).mul cdfZero)
  have residualConverges : Tendsto (fun time : ℝ =>
      ((∫ sample, potential (holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample) time)
          ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) - potential initial) / time -
        ((1 - Real.exp (-(degree endpoint initial * time))) / time) * rateOneGenerator endpoint potential initial)
      (𝓝[>] 0) (𝓝 0) := by
    apply squeeze_zero_norm' _ remainderConverges
    filter_upwards [self_mem_nhdsWithin] with time timePositive
    have estimate := finiteVariableSpeedWalkSampleLaw_generator_estimate endpoint positiveDegree initial potential
      constant constantNonnegative bound maximumRate maximumRateNonnegative degreeBound time timePositive.le
    have identity :
        ((∫ sample, potential (holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample) time)
            ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) - potential initial) / time -
          ((1 - Real.exp (-(degree endpoint initial * time))) / time) * rateOneGenerator endpoint potential initial =
        ((∫ sample, potential (holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample) time)
            ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) -
          (potential initial + (1 - Real.exp (-(degree endpoint initial * time))) *
            rateOneGenerator endpoint potential initial)) / time := by ring
    rw [Real.norm_eq_abs, identity, abs_div]
    rw [show |time| = time from abs_of_pos timePositive]
    calc
      _ ≤ (2 * constant * (1 - Real.exp (-(maximumRate * time))) ^ 2) / time :=
        div_le_div_of_nonneg_right estimate timePositive.le
      _ = _ := by ring
  have generatorEquality : degree endpoint initial * rateOneGenerator endpoint potential initial =
      laplacian endpoint potential initial := by
    unfold rateOneGenerator
    field_simp [(positiveDegree initial).ne']
  simpa only [sub_add_cancel, zero_add, generatorEquality] using
    residualConverges.add ((exponential_cdf_rate_slope (degree endpoint initial)).mul_const
      (rateOneGenerator endpoint potential initial))

theorem finiteVariableSpeedWalkSampleLaw_generator [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) :
    Tendsto (fun time : ℝ =>
      ((∫ sample, potential (holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample) time)
          ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) - potential initial) / time)
      (𝓝[>] 0) (𝓝 (laplacian endpoint potential initial)) := by
  apply finiteVariableSpeedWalkSampleLaw_generator_bounded endpoint positiveDegree initial potential
    (∑ vertex, |potential vertex|) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
    (fun vertex => Finset.single_le_sum (f := fun vertex : Vertex => |potential vertex|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ vertex))
    (∑ vertex, degree endpoint vertex) (Finset.sum_nonneg (fun vertex _ => degree_nonnegative endpoint vertex))
  intro vertex
  exact Finset.single_le_sum (f := degree endpoint) (fun vertex _ => degree_nonnegative endpoint vertex)
    (Finset.mem_univ vertex)

theorem actualFiniteVariableSpeedWalkSampleLaw_generator (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth)
    (potential : ActualFiniteCluster rule configuration scale scalePositive depth → ℝ) :
    Tendsto (fun time : ℝ =>
      ((∫ sample, potential (holdingTimePath sample.1
          (variableSpeedHoldingTimes
            (degree (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))) sample) time)
          ∂finiteContinuousWalkSampleLaw
            (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
            (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
            (cluster_degree_positive (rule.generation depth).network (configuration depth) (crossing depth))
            (Measure.dirac initial)) - potential initial) / time) (𝓝[>] 0)
      (𝓝 (laplacian (clusterRetainedEndpoint (rule.generation depth).network (configuration depth)) potential initial)) :=
  finiteVariableSpeedWalkSampleLaw_generator _ _ initial potential

end
end IGSIII34.Diffusion
