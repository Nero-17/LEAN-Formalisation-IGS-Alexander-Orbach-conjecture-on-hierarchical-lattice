import IGSIII34.Diffusion.ContinuousWalkConstruction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

def variableSpeedHoldingTimes {Vertex : Type*} (rate : Vertex → ℝ)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) (index : ℕ) : ℝ :=
  sample.2 index / rate (sample.1 index)

theorem variableSpeedHoldingTimes_measurable {Vertex : Type*} [MeasurableSpace Vertex]
    (rate : Vertex → ℝ) (rateMeasurable : Measurable rate) :
    Measurable (variableSpeedHoldingTimes rate) := by
  apply measurable_pi_lambda
  intro index
  exact ((measurable_pi_apply index).comp measurable_snd).div
    (rateMeasurable.comp ((measurable_pi_apply index).comp measurable_fst))

theorem variableSpeedHoldingTimes_positive {Vertex : Type*} (rate : Vertex → ℝ)
    (ratePositive : ∀ vertex, 0 < rate vertex) (sample : (ℕ → Vertex) × (ℕ → ℝ))
    (positive : ∀ index, 0 < sample.2 index) : ∀ index, 0 < variableSpeedHoldingTimes rate sample index := by
  intro index
  exact div_pos (positive index) (ratePositive _)

theorem variableSpeedHoldingTimes_nonexplosion {Vertex : Type*} [Fintype Vertex]
    (rate : Vertex → ℝ) (ratePositive : ∀ vertex, 0 < rate vertex)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) (positive : ∀ index, 0 < sample.2 index)
    (nonexplosion : Tendsto (cumulativeHoldingTime sample.2) atTop atTop) :
    Tendsto (cumulativeHoldingTime (variableSpeedHoldingTimes rate sample)) atTop atTop := by
  have totalPositive : 0 < 1 + ∑ vertex, rate vertex :=
    add_pos_of_pos_of_nonneg zero_lt_one (Finset.sum_nonneg (fun vertex _ => (ratePositive vertex).le))
  have lower : ∀ count, (1 + ∑ vertex, rate vertex)⁻¹ * cumulativeHoldingTime sample.2 count ≤
      cumulativeHoldingTime (variableSpeedHoldingTimes rate sample) count := by
    intro count
    unfold cumulativeHoldingTime
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index _
    rw [mul_comm, ← div_eq_mul_inv]
    apply div_le_div_of_nonneg_left (positive index).le (ratePositive _)
    exact (Finset.single_le_sum (fun vertex _ => (ratePositive vertex).le) (Finset.mem_univ _)).trans
      (le_add_of_nonneg_left (by norm_num))
  exact tendsto_atTop_mono lower (nonexplosion.const_mul_atTop (inv_pos.mpr totalPositive))

def finiteVariableSpeedWalkPath {Vertex : Type*} (rate : Vertex → ℝ)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) (time : ℝ≥0) : Vertex :=
  holdingTimePath sample.1 (variableSpeedHoldingTimes rate sample) time

theorem finiteVariableSpeedWalkPath_measurable {Vertex : Type*} [MeasurableSpace Vertex]
    (rate : Vertex → ℝ) (rateMeasurable : Measurable rate) :
    Measurable (finiteVariableSpeedWalkPath rate) := by
  apply measurable_pi_lambda
  intro time
  exact (holdingTimePath_measurable time).comp
    (measurable_fst.prodMk (variableSpeedHoldingTimes_measurable rate rateMeasurable))

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

/-- A genuine variable-speed law: an independent exponential variable is
divided by the current vertex degree before every jump. Thus the total jump
rate is the degree, corresponding to rate one per incident edge. -/
def finiteVariableSpeedWalkLaw (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) :
    Measure (ℝ≥0 → Vertex) :=
  (finiteContinuousWalkSampleLaw endpoint positiveDegree initial).map
    (finiteVariableSpeedWalkPath (degree endpoint))

instance finiteVariableSpeedWalkLaw_probability (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex)
    [IsProbabilityMeasure initial] : IsProbabilityMeasure (finiteVariableSpeedWalkLaw endpoint positiveDegree initial) := by
  unfold finiteVariableSpeedWalkLaw
  exact isProbabilityMeasure_map
    (finiteVariableSpeedWalkPath_measurable _ (measurable_of_countable _)).aemeasurable

theorem finiteVariableSpeedWalkSampleLaw_regular (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) :
    ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree initial,
      (∀ index, 0 < variableSpeedHoldingTimes (degree endpoint) sample index) ∧
      Tendsto (cumulativeHoldingTime (variableSpeedHoldingTimes (degree endpoint) sample)) atTop atTop := by
  filter_upwards [finiteContinuousWalkSampleLaw_regular endpoint positiveDegree initial] with sample regular
  exact ⟨variableSpeedHoldingTimes_positive _ positiveDegree sample regular.1,
    variableSpeedHoldingTimes_nonexplosion _ positiveDegree sample regular.1 regular.2.1⟩

theorem finiteVariableSpeedWalkLaw_initial (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) :
    (finiteVariableSpeedWalkLaw endpoint positiveDegree initial).map (fun path => path 0) = initial := by
  rw [finiteVariableSpeedWalkLaw, Measure.map_map (measurable_pi_apply 0)
    (finiteVariableSpeedWalkPath_measurable _ (measurable_of_countable _))]
  have equality : (fun sample : (ℕ → Vertex) × (ℕ → ℝ) =>
      finiteVariableSpeedWalkPath (degree endpoint) sample 0) =ᵐ[
        finiteContinuousWalkSampleLaw endpoint positiveDegree initial] fun sample => sample.1 0 := by
    filter_upwards [finiteVariableSpeedWalkSampleLaw_regular endpoint positiveDegree initial] with sample regular
    exact holdingTimePath_initial _ _ regular.1
  change (finiteContinuousWalkSampleLaw endpoint positiveDegree initial).map
    (fun sample => finiteVariableSpeedWalkPath (degree endpoint) sample 0) = initial
  rw [Measure.map_congr equality]
  calc
    _ = ((finiteContinuousWalkSampleLaw endpoint positiveDegree initial).map Prod.fst).map
        (fun trajectory => trajectory 0) := (Measure.map_map (measurable_pi_apply 0) measurable_fst).symm
    _ = initial := by rw [finiteContinuousWalkSampleLaw_discreteTrajectory, finiteDiscreteWalkLaw_initial]

def actualFiniteVariableSpeedWalkLaw (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) :
    Measure (ℝ≥0 → ActualFiniteCluster rule configuration scale scalePositive depth) :=
  finiteVariableSpeedWalkLaw
    (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
    (cluster_degree_positive (rule.generation depth).network (configuration depth) (crossing depth))
    (Measure.dirac initial)

instance actualFiniteVariableSpeedWalkLaw_probability (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) :
    IsProbabilityMeasure (actualFiniteVariableSpeedWalkLaw rule configuration crossing scale scalePositive depth initial) := by
  unfold actualFiniteVariableSpeedWalkLaw
  infer_instance

theorem actualFiniteVariableSpeedWalkLaw_initial (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) :
    (actualFiniteVariableSpeedWalkLaw rule configuration crossing scale scalePositive depth initial).map
      (fun path => path 0) = Measure.dirac initial := finiteVariableSpeedWalkLaw_initial _ _ _

end
end IGSIII34.Diffusion
