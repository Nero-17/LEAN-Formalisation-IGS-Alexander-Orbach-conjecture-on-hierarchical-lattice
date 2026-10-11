import IGSIII34.Diffusion.WalkQuadraticVariationCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped _root_.Topology BigOperators NNReal
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [StandardBorelSpace Vertex] [Nonempty Vertex]

theorem finiteWalk_squared_increment_telescopes_completion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ) (time : ℕ) :
    (∫ path, (potential (path (time+1)) - potential (path time)) ^ 2 ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
      (∫ path, potential (path (time+1)) ^ 2 ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) -
      (∫ path, potential (path time) ^ 2 ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) -
      2 * ∫ path, potential (path time) * rateOneGenerator endpoint potential (path time) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial := by
  let law := finiteDiscreteWalkLaw endpoint positiveDegree initial
  let current := fun path : ℕ → Vertex => potential (path time)
  let next := fun path : ℕ → Vertex => potential (path (time+1))
  let increment := fun path : ℕ → Vertex => potential (path (time+1)) - transition endpoint potential (path time)
  let drift := fun path : ℕ → Vertex => rateOneGenerator endpoint potential (path time)
  have currentLp : MemLp current 2 law := finitePathPotential_memLp_completion20261011 _ potential time 2
  have nextLp : MemLp next 2 law := finitePathPotential_memLp_completion20261011 _ potential (time+1) 2
  have incrementLp : MemLp increment 2 law := nextLp.sub (finitePathPotential_memLp_completion20261011 _ (transition endpoint potential) time 2)
  have driftLp : MemLp drift 2 law := finitePathPotential_memLp_completion20261011 _ (rateOneGenerator endpoint potential) time 2
  have zeroProduct := squareIntegrable_past_zeroMean_product_completion20261011 law (Filtration.piLE time) (Filtration.piLE.le time)
    current increment (finitePathPotential_stronglyMeasurable_past_completion20261011 potential time time le_rfl)
    currentLp incrementLp (walkCompensatedPotential_increment_mean_zero_completion20261011 endpoint positiveDegree initial potential time)
  have crossIntegrable : Integrable (fun path => current path * increment path) law := memLp_one_iff_integrable.mp (incrementLp.mul currentLp)
  have driftIntegrable : Integrable (fun path => current path * drift path) law := memLp_one_iff_integrable.mp (driftLp.mul currentLp)
  have identity : (fun path : ℕ → Vertex => (potential (path (time+1)) - potential (path time)) ^ 2) =
      fun path => next path ^ 2 - current path ^ 2 - 2 * (current path * increment path) - 2 * (current path * drift path) := by
    funext path
    dsimp [current, next, increment, drift, transition]
    ring
  change (∫ path, (potential (path (time+1)) - potential (path time)) ^ 2 ∂law) = _
  have splitOuter : (∫ path, next path ^ 2 - current path ^ 2 - 2 * (current path * increment path) - 2 * (current path * drift path) ∂law) =
      (∫ path, next path ^ 2 - current path ^ 2 - 2 * (current path * increment path) ∂law) -
        ∫ path, 2 * (current path * drift path) ∂law :=
    integral_sub ((nextLp.integrable_sq.sub currentLp.integrable_sq).sub (crossIntegrable.const_mul 2)) (driftIntegrable.const_mul 2)
  have splitCross : (∫ path, next path ^ 2 - current path ^ 2 - 2 * (current path * increment path) ∂law) =
      (∫ path, next path ^ 2 - current path ^ 2 ∂law) - ∫ path, 2 * (current path * increment path) ∂law :=
    integral_sub (nextLp.integrable_sq.sub currentLp.integrable_sq) (crossIntegrable.const_mul 2)
  have splitSquares : (∫ path, next path ^ 2 - current path ^ 2 ∂law) =
      (∫ path, next path ^ 2 ∂law) - (∫ path, current path ^ 2 ∂law) :=
    integral_sub nextLp.integrable_sq currentLp.integrable_sq
  rw [identity, splitOuter, splitCross, splitSquares, integral_const_mul, integral_const_mul, zeroProduct]
  simp only [mul_zero, sub_zero]
  rfl

theorem finiteWalk_compensated_square_bound_nonstationary_completion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial] (potential : Vertex → ℝ)
    (size driftBound : ℝ) (sizeNonnegative : 0 ≤ size) (driftNonnegative : 0 ≤ driftBound)
    (potentialBound : ∀ vertex, |potential vertex| ≤ size)
    (generatorBound : ∀ vertex, |rateOneGenerator endpoint potential vertex| ≤ driftBound) (time : ℕ) :
    (∫ path, walkCompensatedPotential endpoint potential time path ^ 2 ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) ≤
      size ^ 2 + 2 * time * size * driftBound := by
  let law := finiteDiscreteWalkLaw endpoint positiveDegree initial
  have refined : ∀ time : ℕ, (∫ path, walkCompensatedPotential endpoint potential time path ^ 2 ∂law) ≤
      (∫ path, potential (path time) ^ 2 ∂law) + 2 * time * size * driftBound := by
    intro time
    induction time with
    | zero =>
        simp only [walkCompensatedPotential, Finset.sum_range_zero, sub_self, sub_zero, zero_pow (by decide : 2 ≠ 0), integral_zero,
          Nat.cast_zero, mul_zero, zero_mul, add_zero]
        exact integral_nonneg fun path => sq_nonneg _
    | succ time induction =>
        have driftIntegralBound : |∫ path, potential (path time) * rateOneGenerator endpoint potential (path time) ∂law| ≤ size * driftBound := by
          have bounded := norm_integral_le_of_norm_le_const (μ := law)
            (f := fun path => potential (path time) * rateOneGenerator endpoint potential (path time))
            (C := size * driftBound) (ae_of_all _ fun path => by
              rw [Real.norm_eq_abs, abs_mul]
              exact mul_le_mul (potentialBound _) (generatorBound _) (abs_nonneg _) sizeNonnegative)
          simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using bounded
        have step := walkCompensatedPotential_one_step_square_bound_completion20261011 endpoint positiveDegree initial potential time
        rw [finiteWalk_squared_increment_telescopes_completion20261011] at step
        rw [walkCompensatedPotential_square_step_identity_completion20261011 endpoint positiveDegree initial]
        push_cast
        nlinarith [neg_le_abs (∫ path, potential (path time) * rateOneGenerator endpoint potential (path time) ∂law)]
  have terminalBound : (∫ path, potential (path time) ^ 2 ∂law) ≤ size ^ 2 := by
    have bounded := norm_integral_le_of_norm_le_const (μ := law) (f := fun path => potential (path time) ^ 2)
      (C := size ^ 2) (ae_of_all _ fun path => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith [potentialBound (path time), neg_le_abs (potential (path time)), le_abs_self (potential (path time))])
    have absolute : |∫ path, potential (path time) ^ 2 ∂law| ≤ size ^ 2 := by
      simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using bounded
    exact (le_abs_self _).trans absolute
  exact (refined time).trans (add_le_add terminalBound le_rfl)

end
end IGSIII34.Diffusion

