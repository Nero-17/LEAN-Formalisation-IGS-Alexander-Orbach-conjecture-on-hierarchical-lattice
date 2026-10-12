import IGSIII34.Diffusion.StationaryDegreeWalkCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

/-- Conditional expectations of genuine two-point observables, including
edge increments, are computed from the same entire-past neighbour kernel. -/
theorem finiteDiscreteWalkLaw_conditional_pair_expectation_completion
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (potential : Vertex → Vertex → ℝ) (time : ℕ) :
    (finiteDiscreteWalkLaw endpoint positiveDegree initial)[
      fun path => potential (path time) (path (time + 1)) | Filtration.piLE time] =ᵐ[
        finiteDiscreteWalkLaw endpoint positiveDegree initial]
      fun path => transition endpoint (potential (path time)) (path time) := by
  let observable : (((coordinate : Finset.Iic time) → Vertex) × Vertex) → ℝ :=
    fun pair => potential (pair.1 ⟨time, Finset.mem_Iic.mpr le_rfl⟩) pair.2
  have observableIntegrable : Integrable observable
      ((finiteDiscreteWalkLaw endpoint positiveDegree initial).map
        (fun path => (frestrictLe time path, path (time + 1)))) := Integrable.of_finite
  have composedIntegrable := observableIntegrable.comp_aemeasurable
    ((measurable_frestrictLe time).prodMk (measurable_pi_apply (time + 1))).aemeasurable
  have conditional : (finiteDiscreteWalkLaw endpoint positiveDegree initial)[
      fun path => observable (frestrictLe time path, path (time + 1)) | Filtration.piLE time] =ᵐ[
        finiteDiscreteWalkLaw endpoint positiveDegree initial]
      fun path => ∫ last, observable (frestrictLe time path, last)
        ∂condDistrib (fun path : ℕ → Vertex => path (time + 1)) (frestrictLe time)
          (finiteDiscreteWalkLaw endpoint positiveDegree initial) (frestrictLe time path) := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    exact condExp_prod_ae_eq_integral_condDistrib
      (measurable_frestrictLe time) (measurable_pi_apply (time + 1)).aemeasurable
      (measurable_of_countable observable).stronglyMeasurable composedIntegrable
  have kernelEquality := ae_of_ae_map (measurable_frestrictLe time).aemeasurable
    (finiteDiscreteWalkLaw_condDistrib endpoint positiveDegree initial time)
  filter_upwards [conditional, kernelEquality] with path conditionalEquality kernelEquality
  have observableEquality : (fun path : ℕ → Vertex => observable (frestrictLe time path, path (time + 1))) =
      fun path => potential (path time) (path (time + 1)) := rfl
  rw [observableEquality] at conditionalEquality
  rw [conditionalEquality, kernelEquality]
  change (∫ last, potential (path time) last ∂finiteWalkKernel endpoint positiveDegree (path time)) = _
  exact finiteWalkKernel_integral endpoint positiveDegree (potential (path time)) (path time)

variable [Nonempty Edge]

theorem finiteDiscreteWalkLaw_stationary_pair_integral_completion
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (potential : Vertex → Vertex → ℝ) (time : ℕ) :
    (∫ path, potential (path time) (path (time + 1))
      ∂finiteDiscreteWalkLaw endpoint positiveDegree (degreeMeasure endpoint)) =
      ∑ first, degreeWeight endpoint first *
        ∑ last, transitionKernel endpoint first last * potential first last := by
  calc
    _ = ∫ path, ((finiteDiscreteWalkLaw endpoint positiveDegree (degreeMeasure endpoint))[
        fun path => potential (path time) (path (time + 1)) | Filtration.piLE time]) path
        ∂finiteDiscreteWalkLaw endpoint positiveDegree (degreeMeasure endpoint) :=
      (integral_condExp (Filtration.piLE.le time)).symm
    _ = ∫ path, transition endpoint (potential (path time)) (path time)
        ∂finiteDiscreteWalkLaw endpoint positiveDegree (degreeMeasure endpoint) :=
      integral_congr_ae (finiteDiscreteWalkLaw_conditional_pair_expectation_completion
        endpoint positiveDegree (degreeMeasure endpoint) potential time)
    _ = ∫ first, transition endpoint (potential first) first ∂degreeMeasure endpoint :=
      finiteDiscreteWalkLaw_degree_integral endpoint positiveDegree time
        (fun first => transition endpoint (potential first) first)
    _ = _ := by
      rw [degreeMeasure_integral]
      simp_rw [transition_eq_kernel endpoint positiveDegree]

theorem transition_squared_difference_completion
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (potential : Vertex → ℝ) (first : Vertex) :
    transition endpoint (fun last => (potential last - potential first) ^ 2) first =
      transition endpoint (fun last => potential last ^ 2) first -
        2 * potential first * transition endpoint potential first + potential first ^ 2 := by
  simp only [transition_eq_kernel endpoint positiveDegree]
  calc
    _ = ∑ last, (transitionKernel endpoint first last * potential last ^ 2 -
        2 * potential first * (transitionKernel endpoint first last * potential last) +
          transitionKernel endpoint first last * potential first ^ 2) := by
      apply Finset.sum_congr rfl
      intro last _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        ← Finset.sum_mul, transitionKernel_sum endpoint first (positiveDegree first), one_mul]

/-- The actual stationary edge-increment quadratic variation is the graph
energy divided by the full number of retained edges. In particular the
natural `2 e λ^n` clock produces the correct scaled energy. -/
theorem stationary_squared_increment_energy_completion
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (potential : Vertex → ℝ) :
    (∑ first, degreeWeight endpoint first *
      transition endpoint (fun last => (potential last - potential first) ^ 2) first) =
        energy endpoint potential / Fintype.card Edge := by
  have stationarySquares :
      (∑ first, degreeWeight endpoint first * transition endpoint (fun last => potential last ^ 2) first) =
        ∑ first, degreeWeight endpoint first * potential first ^ 2 := by
    simpa only [degreeMeasure_integral] using
      degreeMeasure_transition_integral endpoint positiveDegree (fun last => potential last ^ 2)
  calc
    _ = (∑ first, degreeWeight endpoint first * transition endpoint (fun last => potential last ^ 2) first) -
        (∑ first, degreeWeight endpoint first * potential first ^ 2) +
        2 * ∑ first, degreeWeight endpoint first * (-rateOneGenerator endpoint potential first) * potential first := by
      rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro first _
      rw [transition_squared_difference_completion endpoint positiveDegree]
      simp only [transition]
      ring
    _ = energy endpoint potential / Fintype.card Edge := by
      rw [stationarySquares, sub_self, zero_add, rateOne_energy endpoint positiveDegree]
      field_simp
      <;> ring

theorem finiteDiscreteWalkLaw_stationary_squared_increment_completion
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (potential : Vertex → ℝ) (time : ℕ) :
    (∫ path, (potential (path (time + 1)) - potential (path time)) ^ 2
      ∂finiteDiscreteWalkLaw endpoint positiveDegree (degreeMeasure endpoint)) =
        energy endpoint potential / Fintype.card Edge := by
  rw [finiteDiscreteWalkLaw_stationary_pair_integral_completion
    endpoint positiveDegree (fun first last => (potential last - potential first) ^ 2) time]
  simp_rw [← transition_eq_kernel endpoint positiveDegree]
  exact stationary_squared_increment_energy_completion endpoint positiveDegree potential

end
end IGSIII34.Diffusion
