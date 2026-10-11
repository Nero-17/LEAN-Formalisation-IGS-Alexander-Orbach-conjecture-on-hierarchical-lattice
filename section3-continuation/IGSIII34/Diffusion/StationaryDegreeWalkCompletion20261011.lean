import IGSIII34.Diffusion.NaturalClockWalkLaws
import IGSIII.Chemical.SmallBall.FiniteProbability

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex]
  [Fintype Edge] [Nonempty Edge]

instance degreeMeasure_probability_completion20261011
    (endpoint : Edge → Vertex × Vertex) : IsProbabilityMeasure (degreeMeasure endpoint) := by
  unfold degreeMeasure
  infer_instance

theorem degreeMeasure_integral (endpoint : Edge → Vertex × Vertex)
    (potential : Vertex → ℝ) :
    (∫ vertex, potential vertex ∂degreeMeasure endpoint) =
      ∑ vertex, degreeWeight endpoint vertex * potential vertex := by
  exact IGSIII.Chemical.SmallBall.finiteWeight_integral _ _ _ _

theorem degreeMeasure_transition_integral (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (potential : Vertex → ℝ) :
    (∫ vertex, transition endpoint potential vertex ∂degreeMeasure endpoint) =
      ∫ vertex, potential vertex ∂degreeMeasure endpoint := by
  rw [degreeMeasure_integral, degreeMeasure_integral]
  simp_rw [transition_eq_kernel endpoint positiveDegree, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, degree_stationary endpoint positiveDegree]

/-- Every discrete-time marginal of the actual neighbour walk started from
the full degree probability is again the degree probability, stated first as
an integral identity for every potential. -/
theorem finiteDiscreteWalkLaw_degree_integral [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (time : ℕ)
    (potential : Vertex → ℝ) :
    (∫ path, potential (path time)
      ∂finiteDiscreteWalkLaw endpoint positiveDegree (degreeMeasure endpoint)) =
      ∫ vertex, potential vertex ∂degreeMeasure endpoint := by
  induction time generalizing potential with
  | zero =>
    rw [← integral_map (measurable_pi_apply 0).aemeasurable
      (measurable_of_countable potential).aestronglyMeasurable,
      finiteDiscreteWalkLaw_initial]
  | succ time induction =>
    rw [finiteDiscreteWalkLaw_integral_next endpoint positiveDegree
      (degreeMeasure endpoint) potential time, induction,
      degreeMeasure_transition_integral endpoint positiveDegree]

/-- The sample process itself, rather than a presumed semigroup, has the
degree law at every real observation time. Independence of the whole jump
trajectory from all holding times is the only clock input. -/
theorem finiteContinuousWalkSampleLaw_degree_integral [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (time : ℝ)
    (potential : Vertex → ℝ) :
    (∫ sample, potential (holdingTimePath sample.1 sample.2 time)
      ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (degreeMeasure endpoint)) =
      ∫ vertex, potential vertex ∂degreeMeasure endpoint := by
  have measurablePotential : Measurable (fun sample : (ℕ → Vertex) × (ℕ → ℝ) =>
      potential (holdingTimePath sample.1 sample.2 time)) :=
    (measurable_of_countable potential).comp (holdingTimePath_measurable time)
  have bound : ∀ vertex, |potential vertex| ≤ ∑ vertex, |potential vertex| := by
    intro vertex
    exact Finset.single_le_sum (f := fun vertex : Vertex => |potential vertex|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ vertex)
  have integrablePotential : Integrable
      (fun sample : (ℕ → Vertex) × (ℕ → ℝ) =>
        potential (holdingTimePath sample.1 sample.2 time))
      (finiteContinuousWalkSampleLaw endpoint positiveDegree (degreeMeasure endpoint)) :=
    Integrable.of_mem_Icc (-(∑ vertex, |potential vertex|)) (∑ vertex, |potential vertex|)
      measurablePotential.aemeasurable (Eventually.of_forall fun sample => abs_le.mp (bound _))
  rw [finiteContinuousWalkSampleLaw, integral_prod_symm _ integrablePotential]
  simp_rw [holdingTimePath, finiteDiscreteWalkLaw_degree_integral endpoint positiveDegree]
  simp

theorem finiteMeasure_eq_of_all_potential_integrals_completion20261011
    (first last : Measure Vertex) [IsFiniteMeasure first] [IsFiniteMeasure last]
    (integrals : ∀ potential : Vertex → ℝ,
      (∫ vertex, potential vertex ∂first) = ∫ vertex, potential vertex ∂last) :
    first = last := by
  classical
  apply Measure.ext_of_singleton
  intro vertex
  have equality := integrals (({vertex} : Set Vertex).indicator (fun _ => (1 : ℝ)))
  rw [integral_indicator_const _ (measurableSet_singleton vertex),
    integral_indicator_const _ (measurableSet_singleton vertex)] at equality
  simp only [smul_eq_mul, mul_one] at equality
  exact (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp equality

theorem finiteDiscreteWalkLaw_degree_marginal [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (time : ℕ) :
    (finiteDiscreteWalkLaw endpoint positiveDegree (degreeMeasure endpoint)).map
      (fun path => path time) = degreeMeasure endpoint := by
  apply finiteMeasure_eq_of_all_potential_integrals_completion20261011
  intro potential
  rw [integral_map (measurable_pi_apply time).aemeasurable
    (measurable_of_countable potential).aestronglyMeasurable]
  exact finiteDiscreteWalkLaw_degree_integral endpoint positiveDegree time potential

theorem finiteContinuousWalkLaw_degree_marginal [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (time : ℝ≥0) :
    (finiteContinuousWalkLaw endpoint positiveDegree (degreeMeasure endpoint)).map
      (fun path => path time) = degreeMeasure endpoint := by
  rw [finiteContinuousWalkLaw, Measure.map_map (measurable_pi_apply time)
    finiteContinuousWalkPath_measurable]
  apply finiteMeasure_eq_of_all_potential_integrals_completion20261011
  intro potential
  rw [integral_map ((measurable_pi_apply time).comp finiteContinuousWalkPath_measurable).aemeasurable
    (measurable_of_countable potential).aestronglyMeasurable]
  exact finiteContinuousWalkSampleLaw_degree_integral endpoint positiveDegree time potential

/-- Natural finite-volume acceleration preserves the full degree marginal
at each observation time, even when the acceleration depends on volume. -/
theorem naturalDegreeWalkLaw_degree_marginal [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (resistance : ℝ≥0) (depth : ℕ) (time : ℝ≥0) :
    (naturalDegreeWalkLaw endpoint positiveDegree (degreeMeasure endpoint) resistance depth).map
      (fun path => path time) = degreeMeasure endpoint := by
  rw [naturalDegreeWalkLaw, acceleratedFiniteContinuousWalkLaw,
    Measure.map_map (measurable_pi_apply time) (acceleratedPath_measurable _)]
  exact finiteContinuousWalkLaw_degree_marginal endpoint positiveDegree
    ((2 * Fintype.card Edge * resistance ^ depth) * time)

end
end IGSIII34.Diffusion
