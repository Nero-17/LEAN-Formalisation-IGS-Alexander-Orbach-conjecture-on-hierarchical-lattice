import IGSIII34.Diffusion.ActualDegreeMeasure
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

def finiteWalkKernel (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) : Kernel Vertex Vertex :=
  Kernel.ofFunOfCountable fun first =>
    (finiteWeightPMF (transitionKernel endpoint first) (transitionKernel_nonnegative endpoint first)
      (transitionKernel_sum endpoint first (positiveDegree first))).toMeasure

instance finiteWalkKernel_markov (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) : IsMarkovKernel (finiteWalkKernel endpoint positiveDegree) := by
  constructor
  intro first
  change IsProbabilityMeasure (finiteWeightPMF (transitionKernel endpoint first)
    (transitionKernel_nonnegative endpoint first) (transitionKernel_sum endpoint first (positiveDegree first))).toMeasure
  infer_instance

theorem finiteWalkKernel_singleton (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (first last : Vertex) :
    finiteWalkKernel endpoint positiveDegree first {last} = ENNReal.ofReal (transitionKernel endpoint first last) := by
  exact finiteWeightPMF_singleton _ _ _ _

def finiteWalkHistoryKernel (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (time : ℕ) :
    Kernel ((index : Finset.Iic time) → Vertex) Vertex :=
  (finiteWalkKernel endpoint positiveDegree).comap
    (fun history => history ⟨time, Finset.mem_Iic.mpr le_rfl⟩) (measurable_pi_apply _)

instance finiteWalkHistoryKernel_markov (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (time : ℕ) :
    IsMarkovKernel (finiteWalkHistoryKernel endpoint positiveDegree time) := by
  unfold finiteWalkHistoryKernel
  infer_instance

/-- A genuine probability law on infinite discrete walk trajectories,
constructed by the proved Ionescu--Tulcea extension theorem. -/
def finiteDiscreteWalkLaw (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) :
    Measure (ℕ → Vertex) :=
  Kernel.trajMeasure (X := fun _ => Vertex) initial (finiteWalkHistoryKernel endpoint positiveDegree)

instance finiteDiscreteWalkLaw_probability (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Measure Vertex) [IsProbabilityMeasure initial] :
    IsProbabilityMeasure (finiteDiscreteWalkLaw endpoint positiveDegree initial) := by
  unfold finiteDiscreteWalkLaw
  infer_instance

/-- The next-step conditional distribution depends only on the present
vertex, and is exactly the neighbour kernel already identified with the
finite graph generator. -/
theorem finiteDiscreteWalkLaw_condDistrib [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (time : ℕ) :
    condDistrib (fun path : ℕ → Vertex => path (time + 1)) (frestrictLe time)
      (finiteDiscreteWalkLaw endpoint positiveDegree initial) =ᵐ[
        (finiteDiscreteWalkLaw endpoint positiveDegree initial).map (frestrictLe time)]
      finiteWalkHistoryKernel endpoint positiveDegree time :=
  Kernel.condDistrib_trajMeasure

theorem finiteDiscreteWalkLaw_conditional_singleton [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (time : ℕ) (last : Vertex) :
    ∀ᵐ history ∂(finiteDiscreteWalkLaw endpoint positiveDegree initial).map (frestrictLe time),
      condDistrib (fun path : ℕ → Vertex => path (time + 1)) (frestrictLe time)
        (finiteDiscreteWalkLaw endpoint positiveDegree initial) history {last} =
          ENNReal.ofReal (transitionKernel endpoint (history ⟨time, Finset.mem_Iic.mpr le_rfl⟩) last) := by
  filter_upwards [finiteDiscreteWalkLaw_condDistrib endpoint positiveDegree initial time] with history equality
  rw [equality]
  exact finiteWalkKernel_singleton endpoint positiveDegree _ last

/-- The discrete random walk on the same entire retained finite cluster
used by the degree and counting convergence theorems. -/
def actualFiniteDiscreteWalkLaw (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) :
    Measure (ℕ → ActualFiniteCluster rule configuration scale scalePositive depth) :=
  finiteDiscreteWalkLaw (Vertex := ActualFiniteCluster rule configuration scale scalePositive depth)
    (clusterRetainedEndpoint (rule.generation depth).network (configuration depth))
    (cluster_degree_positive (rule.generation depth).network (configuration depth) (crossing depth))
    (Measure.dirac initial)

instance actualFiniteDiscreteWalkLaw_probability (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
    (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (initial : ActualFiniteCluster rule configuration scale scalePositive depth) :
    IsProbabilityMeasure (actualFiniteDiscreteWalkLaw rule configuration crossing scale scalePositive depth initial) := by
  unfold actualFiniteDiscreteWalkLaw
  infer_instance

end
end IGSIII34.Diffusion
