import IGSIII34.Diffusion.AcceleratedWalkLaws

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

def naturalDegreeWalkLaw (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex)
    (resistance : ℝ≥0) (depth : ℕ) : Measure (ℝ≥0 → Vertex) :=
  acceleratedFiniteContinuousWalkLaw endpoint positiveDegree initial
    (2 * Fintype.card Edge * resistance ^ depth)

def naturalCountingWalkLaw (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex)
    (resistance : ℝ≥0) (depth : ℕ) : Measure (ℝ≥0 → Vertex) :=
  acceleratedFiniteVariableSpeedWalkLaw endpoint positiveDegree initial
    (Fintype.card Vertex * resistance ^ depth)

instance naturalDegreeWalkLaw_probability (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex)
    [IsProbabilityMeasure initial] (resistance : ℝ≥0) (depth : ℕ) :
    IsProbabilityMeasure (naturalDegreeWalkLaw endpoint positiveDegree initial resistance depth) := by
  unfold naturalDegreeWalkLaw
  infer_instance

instance naturalCountingWalkLaw_probability (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex)
    [IsProbabilityMeasure initial] (resistance : ℝ≥0) (depth : ℕ) :
    IsProbabilityMeasure (naturalCountingWalkLaw endpoint positiveDegree initial resistance depth) := by
  unfold naturalCountingWalkLaw
  infer_instance

theorem naturalDegreeWalkLaw_initial (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex)
    (resistance : ℝ≥0) (depth : ℕ) :
    (naturalDegreeWalkLaw endpoint positiveDegree initial resistance depth).map (fun path => path 0) = initial :=
  acceleratedFiniteContinuousWalkLaw_initial _ _ _ _

theorem naturalCountingWalkLaw_initial (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex)
    (resistance : ℝ≥0) (depth : ℕ) :
    (naturalCountingWalkLaw endpoint positiveDegree initial resistance depth).map (fun path => path 0) = initial :=
  acceleratedFiniteVariableSpeedWalkLaw_initial _ _ _ _

/-- The true natural-clock continuous walk has initial right derivative
`2 e λ^n (P-I)`, the coefficient used by the exact degree energy identity. -/
theorem naturalDegreeWalkSampleLaw_generator [StandardBorelSpace Vertex] [Nonempty Vertex] [Nonempty Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) (resistance : ℝ) (resistancePositive : 0 < resistance) (depth : ℕ) :
    Tendsto (fun time : ℝ =>
      ((∫ sample, potential (holdingTimePath sample.1 sample.2
          (2 * Fintype.card Edge * resistance ^ depth * time))
          ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) - potential initial) / time)
      (𝓝[>] 0) (𝓝 (2 * Fintype.card Edge * resistance ^ depth * rateOneGenerator endpoint potential initial)) := by
  apply acceleratedFiniteContinuousWalkSampleLaw_generator
  exact mul_pos (mul_pos (by norm_num) (Nat.cast_pos.mpr Fintype.card_pos)) (pow_pos resistancePositive depth)

/-- The actual variable-speed construction has natural-clock initial right
derivative `N λ^n Δ`, the coefficient used by the exact counting energy identity. -/
theorem naturalCountingWalkSampleLaw_generator [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) (resistance : ℝ) (resistancePositive : 0 < resistance) (depth : ℕ) :
    Tendsto (fun time : ℝ =>
      ((∫ sample, potential (holdingTimePath sample.1 (variableSpeedHoldingTimes (degree endpoint) sample)
          (Fintype.card Vertex * resistance ^ depth * time))
          ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) - potential initial) / time)
      (𝓝[>] 0) (𝓝 (Fintype.card Vertex * resistance ^ depth * laplacian endpoint potential initial)) := by
  apply acceleratedFiniteVariableSpeedWalkSampleLaw_generator
  exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (pow_pos resistancePositive depth)

def actualNaturalDegreeWalkLaw (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) (resistance : ℝ≥0) :
    Measure (ℝ≥0 → ActualFiniteCluster rule configuration scale scalePositive depth) :=
  naturalDegreeWalkLaw (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
    (cluster_degree_positive (rule.generation depth).network (configuration depth) (crossing depth))
    (Measure.dirac initial) resistance depth

def actualNaturalCountingWalkLaw (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) (resistance : ℝ≥0) :
    Measure (ℝ≥0 → ActualFiniteCluster rule configuration scale scalePositive depth) :=
  naturalCountingWalkLaw (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
    (cluster_degree_positive (rule.generation depth).network (configuration depth) (crossing depth))
    (Measure.dirac initial) resistance depth

instance actualNaturalDegreeWalkLaw_probability (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) (resistance : ℝ≥0) :
    IsProbabilityMeasure (actualNaturalDegreeWalkLaw rule configuration crossing scale scalePositive depth initial resistance) := by
  unfold actualNaturalDegreeWalkLaw
  infer_instance

instance actualNaturalCountingWalkLaw_probability (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) (resistance : ℝ≥0) :
    IsProbabilityMeasure (actualNaturalCountingWalkLaw rule configuration crossing scale scalePositive depth initial resistance) := by
  unfold actualNaturalCountingWalkLaw
  infer_instance

theorem actualNaturalDegreeWalkLaw_initial (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) (resistance : ℝ≥0) :
    (actualNaturalDegreeWalkLaw rule configuration crossing scale scalePositive depth initial resistance).map
      (fun path => path 0) = Measure.dirac initial := naturalDegreeWalkLaw_initial _ _ _ _ _

theorem actualNaturalCountingWalkLaw_initial (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) (resistance : ℝ≥0) :
    (actualNaturalCountingWalkLaw rule configuration crossing scale scalePositive depth initial resistance).map
      (fun path => path 0) = Measure.dirac initial := naturalCountingWalkLaw_initial _ _ _ _ _

end
end IGSIII34.Diffusion
