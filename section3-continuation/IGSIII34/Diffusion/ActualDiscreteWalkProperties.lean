import IGSIII34.Diffusion.DiscreteWalkProcess

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

theorem finiteDiscreteWalkLaw_initial {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
    [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) :
    (finiteDiscreteWalkLaw endpoint positiveDegree initial).map (fun path => path 0) = initial := by
  have zeroMarginal : (finiteDiscreteWalkLaw endpoint positiveDegree initial).map (frestrictLe 0) =
      initial.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Vertex)).symm := by
    unfold finiteDiscreteWalkLaw Kernel.trajMeasure
    rw [Measure.map_comp _ _ (measurable_frestrictLe 0), Kernel.traj_map_frestrictLe,
      Kernel.partialTraj_self, Measure.id_comp]
  have result := congrArg (fun measure => measure.map
    (fun history : (index : Finset.Iic 0) → Vertex => history ⟨0, Finset.mem_Iic.mpr le_rfl⟩)) zeroMarginal
  have evaluationMeasurable : Measurable
      (fun history : (index : Finset.Iic 0) → Vertex => history ⟨0, Finset.mem_Iic.mpr le_rfl⟩) := measurable_pi_apply _
  rw [Measure.map_map evaluationMeasurable (measurable_frestrictLe 0),
    Measure.map_map evaluationMeasurable (MeasurableEquiv.piUnique _).symm.measurable] at result
  convert result using 1
  · rfl
  · have identity : (fun vertex : Vertex => (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Vertex)).symm vertex
        ⟨0, Finset.mem_Iic.mpr le_rfl⟩) = id := by
      ext vertex
      rfl
    rw [show ((fun history : (index : Finset.Iic 0) → Vertex => history ⟨0, Finset.mem_Iic.mpr le_rfl⟩) ∘
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Vertex)).symm) = id from identity, Measure.map_id]

theorem actualFiniteDiscreteWalkLaw_initial (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) :
    (actualFiniteDiscreteWalkLaw rule configuration crossing scale scalePositive depth initial).map
      (fun path => path 0) = Measure.dirac initial :=
  finiteDiscreteWalkLaw_initial _ _ _

theorem actualFiniteDiscreteWalkLaw_conditional_singleton (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial last : ActualFiniteCluster rule configuration scale scalePositive depth) (time : ℕ) :
    ∀ᵐ history ∂(actualFiniteDiscreteWalkLaw rule configuration crossing scale scalePositive depth initial).map (frestrictLe time),
      condDistrib (fun path : ℕ → ActualFiniteCluster rule configuration scale scalePositive depth => path (time + 1))
        (frestrictLe time) (actualFiniteDiscreteWalkLaw rule configuration crossing scale scalePositive depth initial) history {last} =
          ENNReal.ofReal (transitionKernel (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
            (history ⟨time, Finset.mem_Iic.mpr le_rfl⟩) last) :=
  finiteDiscreteWalkLaw_conditional_singleton _ _ _ time last

end
end IGSIII34.Diffusion
