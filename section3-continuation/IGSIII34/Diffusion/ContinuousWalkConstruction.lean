import IGSIII34.Diffusion.HoldingTimePaths
import IGSIII34.Diffusion.ExponentialHoldingTimes

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

/-- The explicit sample space contains the entire discrete neighbour walk
and an independent sequence of rate-one exponential holding times. -/
def finiteContinuousWalkSampleLaw (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) :
    Measure ((ℕ → Vertex) × (ℕ → ℝ)) :=
  (finiteDiscreteWalkLaw endpoint positiveDegree initial).prod exponentialHoldingTimeLaw

instance finiteContinuousWalkSampleLaw_probability (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] :
    IsProbabilityMeasure (finiteContinuousWalkSampleLaw endpoint positiveDegree initial) := by
  unfold finiteContinuousWalkSampleLaw
  infer_instance

theorem finiteContinuousWalkSampleLaw_independent (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] :
    IndepFun (Prod.fst : (ℕ → Vertex) × (ℕ → ℝ) → (ℕ → Vertex)) Prod.snd
      (finiteContinuousWalkSampleLaw endpoint positiveDegree initial) :=
  indepFun_prod (X := id) (Y := id) measurable_id measurable_id

theorem finiteContinuousWalkSampleLaw_holdingTimes (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] :
    (finiteContinuousWalkSampleLaw endpoint positiveDegree initial).map Prod.snd =
      exponentialHoldingTimeLaw := by
  exact measurePreserving_snd.map_eq

theorem finiteContinuousWalkSampleLaw_discreteTrajectory (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) :
    (finiteContinuousWalkSampleLaw endpoint positiveDegree initial).map Prod.fst =
      finiteDiscreteWalkLaw endpoint positiveDegree initial := by
  exact measurePreserving_fst.map_eq

def finiteContinuousWalkPath {Vertex : Type*}
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) (time : ℝ≥0) : Vertex :=
  holdingTimePath sample.1 sample.2 time

omit [Fintype Vertex] [DecidableEq Vertex] [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] in
theorem finiteContinuousWalkPath_at_jump (sample : (ℕ → Vertex) × (ℕ → ℝ))
    (positive : ∀ index, 0 < sample.2 index) (count : ℕ) :
    holdingTimePath sample.1 sample.2 (cumulativeHoldingTime sample.2 count) = sample.1 count := by
  have upper : cumulativeHoldingTime sample.2 count < cumulativeHoldingTime sample.2 (count + 1) := by
    simp only [cumulativeHoldingTime, Finset.sum_range_succ]
    exact lt_add_of_pos_right _ (positive count)
  unfold holdingTimePath
  rw [holdingJumpIndex_eq_of_interval sample.2 (fun index => (positive index).le)
    (cumulativeHoldingTime sample.2 count) count le_rfl upper]

omit [Fintype Vertex] [DecidableEq Vertex] [MeasurableSingletonClass Vertex] in
theorem finiteContinuousWalkPath_measurable :
    Measurable (finiteContinuousWalkPath (Vertex := Vertex)) := by
  apply measurable_pi_lambda
  intro time
  exact holdingTimePath_measurable time

/-- A genuine probability law on real-time trajectories, constructed from
the discrete path law and independent exponential waiting times. The
continuous-time Markov and generator identities are separate obligations. -/
def finiteContinuousWalkLaw (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) :
    Measure (ℝ≥0 → Vertex) :=
  (finiteContinuousWalkSampleLaw endpoint positiveDegree initial).map finiteContinuousWalkPath

instance finiteContinuousWalkLaw_probability (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] :
    IsProbabilityMeasure (finiteContinuousWalkLaw endpoint positiveDegree initial) := by
  unfold finiteContinuousWalkLaw
  exact isProbabilityMeasure_map finiteContinuousWalkPath_measurable.aemeasurable

theorem finiteContinuousWalkSampleLaw_regular (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) :
    ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree initial,
      (∀ index, 0 < sample.2 index) ∧
      Tendsto (cumulativeHoldingTime sample.2) atTop atTop ∧
      ∀ time : ℝ≥0, ∃ intervalLength : ℝ, 0 < intervalLength ∧
        ∀ nextTime : ℝ≥0, time ≤ nextTime → (nextTime : ℝ) < time + intervalLength →
          finiteContinuousWalkPath sample nextTime = finiteContinuousWalkPath sample time := by
  have positive := (quasiMeasurePreserving_snd
    (μ := finiteDiscreteWalkLaw endpoint positiveDegree initial) (ν := exponentialHoldingTimeLaw)).ae
    exponentialHoldingTimeLaw_positive
  have nonexplosion := (quasiMeasurePreserving_snd
    (μ := finiteDiscreteWalkLaw endpoint positiveDegree initial) (ν := exponentialHoldingTimeLaw)).ae
    exponentialHoldingTimeLaw_nonexplosion
  filter_upwards [positive, nonexplosion] with sample positive nonexplosion
  refine ⟨positive, nonexplosion, fun time => ?_⟩
  obtain ⟨intervalLength, intervalPositive, constant⟩ := holdingTimePath_locally_constant_right
    sample.1 sample.2 positive nonexplosion time time.property
  exact ⟨intervalLength, intervalPositive, fun nextTime lower upper => constant nextTime lower upper⟩

theorem finiteContinuousWalkLaw_initial (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) :
    (finiteContinuousWalkLaw endpoint positiveDegree initial).map (fun path => path 0) = initial := by
  rw [finiteContinuousWalkLaw, Measure.map_map (measurable_pi_apply 0) finiteContinuousWalkPath_measurable]
  have equality : (fun sample : (ℕ → Vertex) × (ℕ → ℝ) => finiteContinuousWalkPath sample 0) =ᵐ[
      finiteContinuousWalkSampleLaw endpoint positiveDegree initial] fun sample => sample.1 0 := by
    filter_upwards [finiteContinuousWalkSampleLaw_regular endpoint positiveDegree initial] with sample regular
    exact holdingTimePath_initial sample.1 sample.2 regular.1
  change (finiteContinuousWalkSampleLaw endpoint positiveDegree initial).map
    (fun sample => finiteContinuousWalkPath sample 0) = initial
  rw [Measure.map_congr equality]
  calc
    _ = ((finiteContinuousWalkSampleLaw endpoint positiveDegree initial).map Prod.fst).map
        (fun trajectory => trajectory 0) := (Measure.map_map (measurable_pi_apply 0) measurable_fst).symm
    _ = initial := by
      rw [finiteContinuousWalkSampleLaw_discreteTrajectory, finiteDiscreteWalkLaw_initial]

theorem finiteContinuousWalkSampleLaw_left_limits (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) :
    ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree initial,
      ∀ time : ℝ≥0, 0 < time → ∃ intervalLength : ℝ, 0 < intervalLength ∧
        ∃ leftValue : Vertex, ∀ previousTime : ℝ≥0,
          (time : ℝ) - intervalLength < previousTime → previousTime < time →
            finiteContinuousWalkPath sample previousTime = leftValue := by
  filter_upwards [finiteContinuousWalkSampleLaw_regular endpoint positiveDegree initial] with sample regular
  intro time timePositive
  obtain ⟨intervalLength, intervalPositive, leftValue, constant⟩ := holdingTimePath_locally_constant_left
    sample.1 sample.2 regular.1 regular.2.1 time timePositive
  exact ⟨intervalLength, intervalPositive, leftValue,
    fun previousTime lower upper => constant previousTime lower upper⟩

theorem finiteContinuousWalkSampleLaw_right_continuous [TopologicalSpace Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) :
    ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree initial,
      ∀ time : ℝ, 0 ≤ time → ContinuousWithinAt (holdingTimePath sample.1 sample.2) (Set.Ici time) time := by
  filter_upwards [finiteContinuousWalkSampleLaw_regular endpoint positiveDegree initial] with sample regular
  intro time timeNonnegative
  obtain ⟨intervalLength, intervalPositive, constant⟩ := holdingTimePath_locally_constant_right
    sample.1 sample.2 regular.1 regular.2.1 time timeNonnegative
  apply tendsto_const_nhds.congr'
  filter_upwards [Ico_mem_nhdsGE (lt_add_of_pos_right time intervalPositive)] with nextTime bounds
  exact (constant nextTime bounds.1 bounds.2).symm

theorem finiteContinuousWalkSampleLaw_left_limit [TopologicalSpace Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) :
    ∀ᵐ sample ∂finiteContinuousWalkSampleLaw endpoint positiveDegree initial,
      ∀ time : ℝ, 0 < time → ∃ leftValue : Vertex,
        Tendsto (holdingTimePath sample.1 sample.2) (𝓝[Set.Iio time] time) (𝓝 leftValue) := by
  filter_upwards [finiteContinuousWalkSampleLaw_regular endpoint positiveDegree initial] with sample regular
  intro time timePositive
  obtain ⟨intervalLength, intervalPositive, leftValue, constant⟩ := holdingTimePath_locally_constant_left
    sample.1 sample.2 regular.1 regular.2.1 time timePositive
  refine ⟨leftValue, tendsto_const_nhds.congr' ?_⟩
  filter_upwards [Ioo_mem_nhdsLT (sub_lt_self time intervalPositive)] with previousTime bounds
  exact (constant previousTime bounds.1 bounds.2).symm

/-- The constructed exponential-holding-time walk uses the same complete
finite cluster as the actual counting and degree measure limit theorems. -/
def actualFiniteContinuousWalkLaw (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) :
    Measure (ℝ≥0 → ActualFiniteCluster rule configuration scale scalePositive depth) :=
  finiteContinuousWalkLaw (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
    (cluster_degree_positive (rule.generation depth).network (configuration depth) (crossing depth))
    (Measure.dirac initial)

instance actualFiniteContinuousWalkLaw_probability (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) :
    IsProbabilityMeasure (actualFiniteContinuousWalkLaw rule configuration crossing scale scalePositive depth initial) := by
  unfold actualFiniteContinuousWalkLaw
  infer_instance

theorem actualFiniteContinuousWalkLaw_initial (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) :
    (actualFiniteContinuousWalkLaw rule configuration crossing scale scalePositive depth initial).map
      (fun path => path 0) = Measure.dirac initial :=
  finiteContinuousWalkLaw_initial _ _ _

end
end IGSIII34.Diffusion
