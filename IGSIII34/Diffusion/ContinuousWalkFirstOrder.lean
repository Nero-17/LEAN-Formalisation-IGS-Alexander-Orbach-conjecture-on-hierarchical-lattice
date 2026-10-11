import IGSIII34.Diffusion.JumpCountProbabilities
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

theorem finiteDiscreteWalkLaw_integral_next [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ) (time : ℕ) :
    (∫ path, potential (path (time + 1)) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
      ∫ path, transition endpoint potential (path time) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial := by
  calc
    _ = ∫ path, ((finiteDiscreteWalkLaw endpoint positiveDegree initial)[
        fun path => potential (path (time + 1)) | MeasurableSpace.comap (frestrictLe time) inferInstance]) path
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial :=
      (integral_condExp (measurable_frestrictLe time).comap_le).symm
    _ = _ := integral_congr_ae (finiteDiscreteWalkLaw_conditional_expectation
      endpoint positiveDegree initial potential time)

theorem finiteDiscreteWalkLaw_integral_initial (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (initial : Vertex) (potential : Vertex → ℝ) :
    (∫ path, potential (path 0) ∂finiteDiscreteWalkLaw endpoint positiveDegree (Measure.dirac initial)) =
      potential initial := by
  rw [← integral_map (measurable_pi_apply 0).aemeasurable
    (measurable_of_countable potential).aestronglyMeasurable,
    finiteDiscreteWalkLaw_initial, integral_dirac]

theorem finiteDiscreteWalkLaw_integral_first [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) :
    (∫ path, potential (path 1) ∂finiteDiscreteWalkLaw endpoint positiveDegree (Measure.dirac initial)) =
      transition endpoint potential initial := by
  rw [show (1 : ℕ) = 0 + 1 by rfl,
    finiteDiscreteWalkLaw_integral_next endpoint positiveDegree (Measure.dirac initial) potential 0,
    finiteDiscreteWalkLaw_integral_initial]

def firstJumpPotential (potential : Vertex → ℝ) (time : ℝ)
    (sample : (ℕ → Vertex) × (ℕ → ℝ)) : ℝ :=
  if sample.2 0 ≤ time then potential (sample.1 1) else potential (sample.1 0)

theorem firstJumpPotential_measurable (potential : Vertex → ℝ) (time : ℝ) :
    Measurable (firstJumpPotential potential time) := by
  unfold firstJumpPotential
  exact (((measurable_of_countable potential).comp ((measurable_pi_apply 1).comp measurable_fst))).ite
    (measurableSet_le ((measurable_pi_apply 0).comp measurable_snd) measurable_const)
    (((measurable_of_countable potential).comp ((measurable_pi_apply 0).comp measurable_fst)))

theorem firstJumpPotential_integral [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Vertex) (potential : Vertex → ℝ) (time : ℝ) (timeNonnegative : 0 ≤ time) :
    (∫ sample, firstJumpPotential potential time sample
      ∂finiteContinuousWalkSampleLaw endpoint positiveDegree (Measure.dirac initial)) =
        potential initial + (1 - Real.exp (-time)) * rateOneGenerator endpoint potential initial := by
  have initialIntegrable : Integrable (fun path : ℕ → Vertex => potential (path 0))
      (finiteDiscreteWalkLaw endpoint positiveDegree (Measure.dirac initial)) :=
    (show Integrable potential ((finiteDiscreteWalkLaw endpoint positiveDegree (Measure.dirac initial)).map
      (fun path => path 0)) from Integrable.of_finite).comp_aemeasurable (measurable_pi_apply 0).aemeasurable
  have firstIntegrable : Integrable (fun path : ℕ → Vertex => potential (path 1))
      (finiteDiscreteWalkLaw endpoint positiveDegree (Measure.dirac initial)) :=
    (show Integrable potential ((finiteDiscreteWalkLaw endpoint positiveDegree (Measure.dirac initial)).map
      (fun path => path 1)) from Integrable.of_finite).comp_aemeasurable (measurable_pi_apply 1).aemeasurable
  have indicatorIntegrable : Integrable
      (({holdingTimes : ℕ → ℝ | holdingTimes 0 ≤ time}).indicator (fun _ => (1 : ℝ)))
      exponentialHoldingTimeLaw :=
    (integrable_const 1).indicator (measurableSet_le (measurable_pi_apply 0) measurable_const)
  have identity : firstJumpPotential potential time = fun sample : (ℕ → Vertex) × (ℕ → ℝ) =>
      potential (sample.1 0) + (potential (sample.1 1) - potential (sample.1 0)) *
        ({holdingTimes : ℕ → ℝ | holdingTimes 0 ≤ time}).indicator (fun _ => (1 : ℝ)) sample.2 := by
    funext sample
    by_cases jumped : sample.2 0 ≤ time <;> simp [firstJumpPotential, Set.indicator, jumped]
  have liftedInitial : Integrable (fun sample : (ℕ → Vertex) × (ℕ → ℝ) => potential (sample.1 0))
      ((finiteDiscreteWalkLaw endpoint positiveDegree (Measure.dirac initial)).prod exponentialHoldingTimeLaw) :=
    measurePreserving_fst.integrable_comp_of_integrable initialIntegrable
  have liftedDifference : Integrable (fun sample : (ℕ → Vertex) × (ℕ → ℝ) =>
      (potential (sample.1 1) - potential (sample.1 0)) *
        ({holdingTimes : ℕ → ℝ | holdingTimes 0 ≤ time}).indicator (fun _ => (1 : ℝ)) sample.2)
      ((finiteDiscreteWalkLaw endpoint positiveDegree (Measure.dirac initial)).prod exponentialHoldingTimeLaw) :=
    (firstIntegrable.sub initialIntegrable).mul_prod indicatorIntegrable
  rw [identity, finiteContinuousWalkSampleLaw]
  dsimp only
  rw [integral_add liftedInitial liftedDifference,
    integral_fun_fst (fun path : ℕ → Vertex => potential (path 0)), probReal_univ, one_smul,
    integral_prod_mul (fun path : ℕ → Vertex => potential (path 1) - potential (path 0))
      (({holdingTimes : ℕ → ℝ | holdingTimes 0 ≤ time}).indicator (fun _ => (1 : ℝ))),
    integral_sub firstIntegrable initialIntegrable,
    finiteDiscreteWalkLaw_integral_initial, finiteDiscreteWalkLaw_integral_first,
    integral_indicator_const (1 : ℝ) (measurableSet_le (measurable_pi_apply 0) measurable_const),
    smul_eq_mul, mul_one,
    exponentialHoldingTimeLaw_coordinate_cdf 0 time timeNonnegative,
    transition_sub_identity]
  ring

end
end IGSIII34.Diffusion
