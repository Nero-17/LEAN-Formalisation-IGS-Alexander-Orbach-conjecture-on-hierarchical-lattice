import IGSIII34.Diffusion.StationaryDegreeWalkCompletion20261011
import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.CondVar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

theorem finitePathPotential_memLp_completion20261011
    (law : Measure (ℕ → Vertex)) [IsProbabilityMeasure law]
    (potential : Vertex → ℝ) (index : ℕ) (exponent : ENNReal) :
    MemLp (fun path => potential (path index)) exponent law := by
  apply MemLp.of_bound
    (((measurable_of_countable potential).comp (measurable_pi_apply index)).aestronglyMeasurable)
    (∑ vertex, |potential vertex|)
  filter_upwards [] with path
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun vertex : Vertex => |potential vertex|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ (path index))

theorem finitePathPotential_stronglyMeasurable_past_completion20261011
    (potential : Vertex → ℝ) (index time : ℕ) (bound : index ≤ time) :
    StronglyMeasurable[Filtration.piLE time] (fun path : ℕ → Vertex => potential (path index)) := by
  rw [Filtration.piLE_eq_comap_frestrictLe]
  have observable : StronglyMeasurable
      (fun history : (coordinate : Finset.Iic time) → Vertex =>
        potential (history ⟨index, Finset.mem_Iic.mpr bound⟩)) :=
    ((measurable_of_countable potential).comp (measurable_pi_apply _)).stronglyMeasurable
  exact observable.comp_measurable (Measurable.of_comap_le le_rfl)

def walkCompensatedPotential (endpoint : Edge → Vertex × Vertex) (potential : Vertex → ℝ)
    (time : ℕ) (path : ℕ → Vertex) : ℝ :=
  potential (path time) - potential (path 0) -
    ∑ index ∈ Finset.range time, rateOneGenerator endpoint potential (path index)

theorem walkCompensatedPotential_stronglyAdapted (endpoint : Edge → Vertex × Vertex)
    (potential : Vertex → ℝ) : StronglyAdapted Filtration.piLE
      (walkCompensatedPotential endpoint potential) := by
  intro time
  apply StronglyMeasurable.sub
  · exact (finitePathPotential_stronglyMeasurable_past_completion20261011 potential time time le_rfl).sub
      (finitePathPotential_stronglyMeasurable_past_completion20261011 potential 0 time (Nat.zero_le time))
  · convert Finset.stronglyMeasurable_sum (Finset.range time) (fun index membership =>
      finitePathPotential_stronglyMeasurable_past_completion20261011
        (rateOneGenerator endpoint potential) index time (Finset.mem_range.mp membership).le) using 1
    funext path
    simp only [Finset.sum_apply]

theorem walkCompensatedPotential_memLp (endpoint : Edge → Vertex × Vertex)
    (law : Measure (ℕ → Vertex)) [IsProbabilityMeasure law]
    (potential : Vertex → ℝ) (time : ℕ) (exponent : ENNReal) :
    MemLp (walkCompensatedPotential endpoint potential time) exponent law := by
  apply (finitePathPotential_memLp_completion20261011 law potential time exponent).sub
    (finitePathPotential_memLp_completion20261011 law potential 0 exponent) |>.sub
  exact memLp_finsetSum _ fun index _ =>
    finitePathPotential_memLp_completion20261011 law (rateOneGenerator endpoint potential) index exponent

theorem walkCompensatedPotential_step (endpoint : Edge → Vertex × Vertex)
    (potential : Vertex → ℝ) (time : ℕ) (path : ℕ → Vertex) :
    walkCompensatedPotential endpoint potential (time + 1) path -
      walkCompensatedPotential endpoint potential time path =
        potential (path (time + 1)) - transition endpoint potential (path time) := by
  simp only [walkCompensatedPotential, Finset.sum_range_succ, transition]
  ring

/-- The genuine neighbour trajectory law solves its compensated graph
martingale problem, relative to its complete past. No limiting martingale
or process existence is taken as a premise. -/
theorem finiteDiscreteWalkLaw_compensated_martingale
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ) :
    Martingale (walkCompensatedPotential endpoint potential) Filtration.piLE
      (finiteDiscreteWalkLaw endpoint positiveDegree initial) := by
  apply martingale_of_condExp_sub_eq_zero_nat
    (walkCompensatedPotential_stronglyAdapted endpoint potential)
    (fun time => (walkCompensatedPotential_memLp endpoint
      (finiteDiscreteWalkLaw endpoint positiveDegree initial) potential time 1).integrable le_rfl)
  intro time
  have nextIntegrable := (finitePathPotential_memLp_completion20261011
    (finiteDiscreteWalkLaw endpoint positiveDegree initial) potential (time + 1) 1).integrable le_rfl
  have transitionIntegrable := (finitePathPotential_memLp_completion20261011
    (finiteDiscreteWalkLaw endpoint positiveDegree initial) (transition endpoint potential) time 1).integrable le_rfl
  have stepEquality :
      walkCompensatedPotential endpoint potential (time + 1) -
        walkCompensatedPotential endpoint potential time =
      fun path : ℕ → Vertex => potential (path (time + 1)) - transition endpoint potential (path time) := by
    funext path
    exact walkCompensatedPotential_step endpoint potential time path
  rw [stepEquality]
  have conditional : (finiteDiscreteWalkLaw endpoint positiveDegree initial)[
      fun path => potential (path (time + 1)) | Filtration.piLE time] =ᵐ[
        finiteDiscreteWalkLaw endpoint positiveDegree initial]
      fun path => transition endpoint potential (path time) := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    exact finiteDiscreteWalkLaw_conditional_expectation endpoint positiveDegree initial potential time
  have transitionMeasurable := finitePathPotential_stronglyMeasurable_past_completion20261011
    (transition endpoint potential) time time le_rfl
  filter_upwards [condExp_sub nextIntegrable transitionIntegrable (Filtration.piLE time), conditional]
    with path subtract conditional
  change (finiteDiscreteWalkLaw endpoint positiveDegree initial)[
    (fun path => potential (path (time + 1))) - (fun path => transition endpoint potential (path time)) |
      Filtration.piLE time] path = 0
  rw [subtract]
  simp only [Pi.sub_apply]
  rw [conditional,
    condExp_of_stronglyMeasurable (Filtration.piLE.le time) transitionMeasurable transitionIntegrable]
  simp

/-- Square-integrability makes the actual compensated graph martingale a
nonnegative square submartingale, so the library's proved Doob inequality
can be applied to its complete-past filtration. -/
theorem finiteDiscreteWalkLaw_compensated_square_submartingale
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ) :
    Submartingale (fun time path => (walkCompensatedPotential endpoint potential time path) ^ 2)
      Filtration.piLE (finiteDiscreteWalkLaw endpoint positiveDegree initial) := by
  have martingale := finiteDiscreteWalkLaw_compensated_martingale endpoint positiveDegree initial potential
  refine ⟨fun time => (martingale.stronglyMeasurable time).pow 2, ?_,
    fun time => (walkCompensatedPotential_memLp endpoint
      (finiteDiscreteWalkLaw endpoint positiveDegree initial) potential time 2).integrable_sq⟩
  intro first last bound
  have variance := condVar_ae_eq_condExp_sq_sub_sq_condExp (Filtration.piLE.le first)
    (walkCompensatedPotential_memLp endpoint
      (finiteDiscreteWalkLaw endpoint positiveDegree initial) potential last 2)
  have nonnegative : 0 ≤ᵐ[finiteDiscreteWalkLaw endpoint positiveDegree initial]
      condVar (Filtration.piLE first) (walkCompensatedPotential endpoint potential last)
        (finiteDiscreteWalkLaw endpoint positiveDegree initial) :=
    condExp_nonneg (Eventually.of_forall fun _ => sq_nonneg _)
  filter_upwards [variance, nonnegative, martingale.condExp_ae_eq bound]
    with path variance nonnegative conditional
  simp only [Pi.sub_apply, Pi.pow_apply] at variance
  simp only [Pi.zero_apply] at nonnegative
  rw [conditional] at variance
  change walkCompensatedPotential endpoint potential first path ^ 2 ≤
    (finiteDiscreteWalkLaw endpoint positiveDegree initial)[
      walkCompensatedPotential endpoint potential last ^ 2 | Filtration.piLE first] path
  linarith

theorem finiteDiscreteWalkLaw_compensated_maximal_bound
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ)
    (radius : ℝ) (radiusPositive : 0 < radius) (time : ℕ) :
    ENNReal.ofReal (radius ^ 2) *
      (finiteDiscreteWalkLaw endpoint positiveDegree initial)
        {path | ∃ index ≤ time, radius ≤ |walkCompensatedPotential endpoint potential index path|} ≤
      ENNReal.ofReal (∫ path, (walkCompensatedPotential endpoint potential time path) ^ 2
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) := by
  have squared := finiteDiscreteWalkLaw_compensated_square_submartingale endpoint positiveDegree initial potential
  have nonnegative : 0 ≤ (fun time path => (walkCompensatedPotential endpoint potential time path) ^ 2) :=
    fun _ _ => sq_nonneg _
  have maximal := maximal_ineq squared nonnegative (ε := ⟨radius ^ 2, sq_nonneg radius⟩) time
  change ENNReal.ofNNReal (NNReal.mk (radius ^ 2) (sq_nonneg radius)) *
      (finiteDiscreteWalkLaw endpoint positiveDegree initial)
        {path | radius ^ 2 ≤ (Finset.range (time + 1)).sup' Finset.nonempty_range_add_one
          (fun index => (walkCompensatedPotential endpoint potential index path) ^ 2)} ≤
      ENNReal.ofReal (∫ path in
        {path | radius ^ 2 ≤ (Finset.range (time + 1)).sup' Finset.nonempty_range_add_one
          (fun index => (walkCompensatedPotential endpoint potential index path) ^ 2)},
        (walkCompensatedPotential endpoint potential time path) ^ 2
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) at maximal
  rw [← ENNReal.ofReal_eq_coe_nnreal (sq_nonneg radius)] at maximal
  have eventEquality : {path : ℕ → Vertex | radius ^ 2 ≤
      (Finset.range (time + 1)).sup' Finset.nonempty_range_add_one
        (fun index => (walkCompensatedPotential endpoint potential index path) ^ 2)} =
      {path | ∃ index ≤ time, radius ≤ |walkCompensatedPotential endpoint potential index path|} := by
    ext path
    simp only [Set.mem_setOf_eq, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff,
      sq_le_sq, abs_of_pos radiusPositive]
  rw [eventEquality] at maximal
  have integralBound := setIntegral_le_integral
    (s := {path | ∃ index ≤ time, radius ≤ |walkCompensatedPotential endpoint potential index path|})
    ((walkCompensatedPotential_memLp endpoint (finiteDiscreteWalkLaw endpoint positiveDegree initial)
      potential time 2).integrable_sq)
    (Eventually.of_forall fun _ => sq_nonneg _)
  exact maximal.trans (ENNReal.ofReal_le_ofReal integralBound)

end
end IGSIII34.Diffusion
