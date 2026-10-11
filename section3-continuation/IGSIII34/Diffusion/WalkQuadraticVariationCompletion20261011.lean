import IGSIII34.Diffusion.WalkMartingaleCompletion20261011
import IGSIII34.Diffusion.WalkEnergyIncrementCompletion20261011

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

theorem squareIntegrable_past_zeroMean_product_completion20261011
    {Sample : Type*} [ambient : MeasurableSpace Sample]
    (law : Measure Sample) [IsProbabilityMeasure law]
    (information : MeasurableSpace Sample) (informationLe : information ≤ ambient)
    (past future : Sample → ℝ)
    (pastMeasurable : StronglyMeasurable[information] past)
    (pastSquareIntegrable : MemLp past 2 law) (futureSquareIntegrable : MemLp future 2 law)
    (futureMeanZero : law[future | information] =ᵐ[law] 0) :
    (∫ sample, past sample * future sample ∂law) = 0 := by
  have productIntegrable : Integrable (past * future) law :=
    memLp_one_iff_integrable.mp (futureSquareIntegrable.mul pastSquareIntegrable)
  have pull := condExp_mul_of_stronglyMeasurable_left pastMeasurable
    productIntegrable (futureSquareIntegrable.integrable (by norm_num))
  calc
    _ = ∫ sample, (law[past * future | information]) sample ∂law :=
      (integral_condExp informationLe).symm
    _ = ∫ sample, past sample * (law[future | information]) sample ∂law := by
      apply integral_congr_ae
      filter_upwards [pull] with sample equality
      exact equality
    _ = 0 := by
      calc
        _ = ∫ _sample, (0 : ℝ) ∂law := integral_congr_ae (by
          filter_upwards [futureMeanZero] with sample equality
          simp [equality])
        _ = 0 := integral_zero _ _

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

theorem walkCompensatedPotential_increment_mean_zero_completion20261011
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ) (time : ℕ) :
    (finiteDiscreteWalkLaw endpoint positiveDegree initial)[
      fun path => potential (path (time + 1)) - transition endpoint potential (path time) |
        Filtration.piLE time] =ᵐ[finiteDiscreteWalkLaw endpoint positiveDegree initial] 0 := by
  have nextIntegrable := (finitePathPotential_memLp_completion20261011
    (finiteDiscreteWalkLaw endpoint positiveDegree initial) potential (time + 1) 1).integrable le_rfl
  have transitionIntegrable := (finitePathPotential_memLp_completion20261011
    (finiteDiscreteWalkLaw endpoint positiveDegree initial) (transition endpoint potential) time 1).integrable le_rfl
  have conditional : (finiteDiscreteWalkLaw endpoint positiveDegree initial)[
      fun path => potential (path (time + 1)) | Filtration.piLE time] =ᵐ[
        finiteDiscreteWalkLaw endpoint positiveDegree initial]
      fun path => transition endpoint potential (path time) := by
    rw [Filtration.piLE_eq_comap_frestrictLe]
    exact finiteDiscreteWalkLaw_conditional_expectation endpoint positiveDegree initial potential time
  filter_upwards [condExp_sub nextIntegrable transitionIntegrable (Filtration.piLE time), conditional]
    with path subtract conditional
  change (finiteDiscreteWalkLaw endpoint positiveDegree initial)[
    (fun path => potential (path (time + 1))) - (fun path => transition endpoint potential (path time)) |
      Filtration.piLE time] path = 0
  rw [subtract]
  simp only [Pi.sub_apply]
  rw [conditional, condExp_of_stronglyMeasurable (Filtration.piLE.le time)
    (finitePathPotential_stronglyMeasurable_past_completion20261011 (transition endpoint potential) time time le_rfl)
    transitionIntegrable]
  simp

theorem walkCompensatedPotential_one_step_square_bound_completion20261011
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ) (time : ℕ) :
    (∫ path, (potential (path (time + 1)) - transition endpoint potential (path time)) ^ 2
      ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) ≤
    ∫ path, (potential (path (time + 1)) - potential (path time)) ^ 2
      ∂finiteDiscreteWalkLaw endpoint positiveDegree initial := by
  let martingaleIncrement : (ℕ → Vertex) → ℝ :=
    fun path => potential (path (time + 1)) - transition endpoint potential (path time)
  let drift : (ℕ → Vertex) → ℝ := fun path => rateOneGenerator endpoint potential (path time)
  have incrementSquareIntegrable : MemLp martingaleIncrement 2
      (finiteDiscreteWalkLaw endpoint positiveDegree initial) :=
    (finitePathPotential_memLp_completion20261011 _ potential (time + 1) 2).sub
      (finitePathPotential_memLp_completion20261011 _ (transition endpoint potential) time 2)
  have driftSquareIntegrable : MemLp drift 2 (finiteDiscreteWalkLaw endpoint positiveDegree initial) :=
    finitePathPotential_memLp_completion20261011 _ (rateOneGenerator endpoint potential) time 2
  have zeroProduct := squareIntegrable_past_zeroMean_product_completion20261011
    (finiteDiscreteWalkLaw endpoint positiveDegree initial) (Filtration.piLE time) (Filtration.piLE.le time)
    drift martingaleIncrement
    (finitePathPotential_stronglyMeasurable_past_completion20261011 (rateOneGenerator endpoint potential) time time le_rfl)
    driftSquareIntegrable incrementSquareIntegrable
    (walkCompensatedPotential_increment_mean_zero_completion20261011 endpoint positiveDegree initial potential time)
  have productIntegrable : Integrable (drift * martingaleIncrement)
      (finiteDiscreteWalkLaw endpoint positiveDegree initial) :=
    memLp_one_iff_integrable.mp (incrementSquareIntegrable.mul driftSquareIntegrable)
  have crossIntegrable : Integrable (fun path => drift path * martingaleIncrement path)
      (finiteDiscreteWalkLaw endpoint positiveDegree initial) := productIntegrable
  have doubleIntegrable := crossIntegrable.const_mul 2
  have identity : (fun path : ℕ → Vertex => (potential (path (time + 1)) - potential (path time)) ^ 2) =
      fun path => martingaleIncrement path ^ 2 + 2 * (drift path * martingaleIncrement path) + drift path ^ 2 := by
    funext path
    dsimp [martingaleIncrement, drift, transition]
    ring
  have splitOuter :
      (∫ path, martingaleIncrement path ^ 2 + 2 * (drift path * martingaleIncrement path) + drift path ^ 2
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
      (∫ path, martingaleIncrement path ^ 2 + 2 * (drift path * martingaleIncrement path)
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) +
      ∫ path, drift path ^ 2 ∂finiteDiscreteWalkLaw endpoint positiveDegree initial :=
    integral_add (incrementSquareIntegrable.integrable_sq.add doubleIntegrable) driftSquareIntegrable.integrable_sq
  have splitInner :
      (∫ path, martingaleIncrement path ^ 2 + 2 * (drift path * martingaleIncrement path)
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
      (∫ path, martingaleIncrement path ^ 2 ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) +
      ∫ path, 2 * (drift path * martingaleIncrement path)
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial :=
    integral_add incrementSquareIntegrable.integrable_sq doubleIntegrable
  rw [identity, splitOuter, splitInner, integral_const_mul, zeroProduct]
  simp only [mul_zero, add_zero]
  exact le_add_of_nonneg_right (integral_nonneg fun _ => sq_nonneg _)

theorem walkCompensatedPotential_square_step_identity_completion20261011
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ) (time : ℕ) :
    (∫ path, walkCompensatedPotential endpoint potential (time + 1) path ^ 2
      ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
      (∫ path, walkCompensatedPotential endpoint potential time path ^ 2
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) +
      ∫ path, (potential (path (time + 1)) - transition endpoint potential (path time)) ^ 2
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial := by
  let current := walkCompensatedPotential endpoint potential time
  let difference : (ℕ → Vertex) → ℝ :=
    fun path => potential (path (time + 1)) - transition endpoint potential (path time)
  have currentSquareIntegrable : MemLp current 2 (finiteDiscreteWalkLaw endpoint positiveDegree initial) :=
    walkCompensatedPotential_memLp endpoint _ potential time 2
  have differenceSquareIntegrable : MemLp difference 2 (finiteDiscreteWalkLaw endpoint positiveDegree initial) :=
    (finitePathPotential_memLp_completion20261011 _ potential (time + 1) 2).sub
      (finitePathPotential_memLp_completion20261011 _ (transition endpoint potential) time 2)
  have zeroProduct := squareIntegrable_past_zeroMean_product_completion20261011
    (finiteDiscreteWalkLaw endpoint positiveDegree initial) (Filtration.piLE time) (Filtration.piLE.le time)
    current difference (walkCompensatedPotential_stronglyAdapted endpoint potential time)
    currentSquareIntegrable differenceSquareIntegrable
    (walkCompensatedPotential_increment_mean_zero_completion20261011 endpoint positiveDegree initial potential time)
  have productIntegrable : Integrable (current * difference)
      (finiteDiscreteWalkLaw endpoint positiveDegree initial) :=
    memLp_one_iff_integrable.mp (differenceSquareIntegrable.mul currentSquareIntegrable)
  have crossIntegrable : Integrable (fun path => current path * difference path)
      (finiteDiscreteWalkLaw endpoint positiveDegree initial) := productIntegrable
  have doubleIntegrable := crossIntegrable.const_mul 2
  have identity : (fun path => walkCompensatedPotential endpoint potential (time + 1) path ^ 2) =
      fun path => current path ^ 2 + 2 * (current path * difference path) + difference path ^ 2 := by
    funext path
    have step := walkCompensatedPotential_step endpoint potential time path
    change walkCompensatedPotential endpoint potential (time + 1) path ^ 2 =
      walkCompensatedPotential endpoint potential time path ^ 2 +
        2 * (walkCompensatedPotential endpoint potential time path *
          (potential (path (time + 1)) - transition endpoint potential (path time))) +
        (potential (path (time + 1)) - transition endpoint potential (path time)) ^ 2
    calc
      _ = (walkCompensatedPotential endpoint potential time path +
          (potential (path (time + 1)) - transition endpoint potential (path time))) ^ 2 := by
        congr 1
        linarith
      _ = _ := by ring
  have splitOuter :
      (∫ path, current path ^ 2 + 2 * (current path * difference path) + difference path ^ 2
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
      (∫ path, current path ^ 2 + 2 * (current path * difference path)
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) +
      ∫ path, difference path ^ 2 ∂finiteDiscreteWalkLaw endpoint positiveDegree initial :=
    integral_add (currentSquareIntegrable.integrable_sq.add doubleIntegrable) differenceSquareIntegrable.integrable_sq
  have splitInner :
      (∫ path, current path ^ 2 + 2 * (current path * difference path)
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
      (∫ path, current path ^ 2 ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) +
      ∫ path, 2 * (current path * difference path)
        ∂finiteDiscreteWalkLaw endpoint positiveDegree initial :=
    integral_add currentSquareIntegrable.integrable_sq doubleIntegrable
  rw [identity, splitOuter, splitInner, integral_const_mul, zeroProduct]
  simp only [mul_zero, add_zero]

  rfl

variable [Nonempty Edge]

/-- Quadratic variation accumulated along the true stationary neighbour
chain is bounded linearly in the number of steps by the full graph energy.
There is no postulated process convergence in the estimate. -/
theorem finiteDiscreteWalkLaw_stationary_compensated_square_bound_completion20261011
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (potential : Vertex → ℝ) (time : ℕ) :
    (∫ path, walkCompensatedPotential endpoint potential time path ^ 2
      ∂finiteDiscreteWalkLaw endpoint positiveDegree (degreeMeasure endpoint)) ≤
        time * (energy endpoint potential / Fintype.card Edge) := by
  induction time with
  | zero => simp [walkCompensatedPotential]
  | succ time induction =>
    rw [walkCompensatedPotential_square_step_identity_completion20261011 endpoint positiveDegree]
    have stepBound := (walkCompensatedPotential_one_step_square_bound_completion20261011
      endpoint positiveDegree (degreeMeasure endpoint) potential time).trans_eq
      (finiteDiscreteWalkLaw_stationary_squared_increment_completion20261011 endpoint positiveDegree potential time)
    calc
      _ ≤ time * (energy endpoint potential / Fintype.card Edge) +
          energy endpoint potential / Fintype.card Edge := add_le_add induction stepBound
      _ = _ := by push_cast; ring

theorem finiteDiscreteWalkLaw_stationary_compensated_oscillation_bound_completion20261011
    [StandardBorelSpace Vertex] [Nonempty Vertex]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (potential : Vertex → ℝ) (radius : ℝ) (radiusPositive : 0 < radius) (time : ℕ) :
    ENNReal.ofReal (radius ^ 2) *
      (finiteDiscreteWalkLaw endpoint positiveDegree (degreeMeasure endpoint))
        {path | ∃ index ≤ time, radius ≤ |walkCompensatedPotential endpoint potential index path|} ≤
      ENNReal.ofReal (time * (energy endpoint potential / Fintype.card Edge)) :=
  (finiteDiscreteWalkLaw_compensated_maximal_bound endpoint positiveDegree
    (degreeMeasure endpoint) potential radius radiusPositive time).trans
    (ENNReal.ofReal_le_ofReal
      (finiteDiscreteWalkLaw_stationary_compensated_square_bound_completion20261011
        endpoint positiveDegree potential time))

end
end IGSIII34.Diffusion
