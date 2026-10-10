import IGSIII34.Diffusion.ContinuousWalkConstruction

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

/-- The embedded jump chain in the explicit continuous-time sample space
retains the exact conditional neighbour law given its entire discrete past. -/
theorem finiteContinuousWalkSampleLaw_jump_conditional_singleton
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (time : ℕ) (last : Vertex) :
    ∀ᵐ history ∂(finiteDiscreteWalkLaw endpoint positiveDegree initial).map (frestrictLe time),
      condDistrib (fun sample : (ℕ → Vertex) × (ℕ → ℝ) => sample.1 (time + 1))
        (fun sample => frestrictLe time sample.1)
        (finiteContinuousWalkSampleLaw endpoint positiveDegree initial) history {last} =
          ENNReal.ofReal (transitionKernel endpoint (history ⟨time, Finset.mem_Iic.mpr le_rfl⟩) last) := by
  have transfer := condDistrib_fst_prod (μ := finiteDiscreteWalkLaw endpoint positiveDegree initial)
    (frestrictLe time) (Y := fun path : ℕ → Vertex => path (time + 1))
    (measurable_pi_apply (time + 1)).aemeasurable exponentialHoldingTimeLaw
  filter_upwards [transfer, finiteDiscreteWalkLaw_conditional_singleton endpoint positiveDegree initial time last]
    with history equality conditional
  rw [equality]
  exact conditional

theorem finiteContinuousWalkSampleLaw_jump_holding_independent
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (time holdingIndex : ℕ) :
    IndepFun (fun sample : (ℕ → Vertex) × (ℕ → ℝ) => sample.1 time)
      (fun sample => sample.2 holdingIndex)
      (finiteContinuousWalkSampleLaw endpoint positiveDegree initial) :=
  (finiteContinuousWalkSampleLaw_independent endpoint positiveDegree initial).comp
    (measurable_pi_apply time) (measurable_pi_apply holdingIndex)

def actualFiniteContinuousWalkSampleLaw (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) :
    Measure ((ℕ → ActualFiniteCluster rule configuration scale scalePositive depth) × (ℕ → ℝ)) :=
  finiteContinuousWalkSampleLaw (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
    (cluster_degree_positive (rule.generation depth).network (configuration depth) (crossing depth))
    (Measure.dirac initial)

instance actualFiniteContinuousWalkSampleLaw_probability (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) :
    IsProbabilityMeasure (actualFiniteContinuousWalkSampleLaw rule configuration crossing scale scalePositive depth initial) := by
  unfold actualFiniteContinuousWalkSampleLaw
  infer_instance

theorem actualFiniteContinuousWalkSampleLaw_jump_conditional_singleton (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial last : ActualFiniteCluster rule configuration scale scalePositive depth) (time : ℕ) :
    ∀ᵐ history ∂(actualFiniteDiscreteWalkLaw rule configuration crossing scale scalePositive depth initial).map (frestrictLe time),
      condDistrib
        (fun sample : (ℕ → ActualFiniteCluster rule configuration scale scalePositive depth) × (ℕ → ℝ) => sample.1 (time + 1))
        (fun sample => frestrictLe time sample.1)
        (actualFiniteContinuousWalkSampleLaw rule configuration crossing scale scalePositive depth initial) history {last} =
          ENNReal.ofReal (transitionKernel (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
            (history ⟨time, Finset.mem_Iic.mpr le_rfl⟩) last) :=
  finiteContinuousWalkSampleLaw_jump_conditional_singleton _ _ _ time last

end
end IGSIII34.Diffusion
