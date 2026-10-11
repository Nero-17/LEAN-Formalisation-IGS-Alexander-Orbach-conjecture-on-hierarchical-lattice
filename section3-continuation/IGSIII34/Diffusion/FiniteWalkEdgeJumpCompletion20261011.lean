import IGSIII34.Diffusion.WalkEnergyIncrementCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

variable {Vertex Edge Carrier : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [StandardBorelSpace Vertex] [Nonempty Vertex] [MetricSpace Carrier]

/-- The actual neighbour kernel assigns zero probability to every pair
whose embedded distance exceeds the largest embedded edge distance. -/
theorem finiteTransitionKernel_zero_of_edge_jump_completion20261011
    (endpoint : Edge → Vertex × Vertex) (embedding : Vertex → Carrier) (jump : ℝ)
    (edgeBound : ∀ edge, dist (embedding (endpoint edge).1) (embedding (endpoint edge).2) ≤ jump)
    (first last : Vertex) (far : jump < dist (embedding first) (embedding last)) :
    transitionKernel endpoint first last = 0 := by
  classical
  have noForward (edge : Edge) : endpoint edge ≠ (first, last) := by
    intro equality
    have bound := edgeBound edge
    rw [equality] at bound
    exact not_lt_of_ge bound far
  have noBackward (edge : Edge) : endpoint edge ≠ (last, first) := by
    intro equality
    have bound := edgeBound edge
    rw [equality, dist_comm] at bound
    exact not_lt_of_ge bound far
  simp only [transitionKernel, edgeMultiplicity, if_neg (noForward _), if_neg (noBackward _),
    add_zero, Finset.sum_const_zero, zero_div]

/-- All steps of the genuine infinite neighbour trajectory satisfy the
proved edge-jump bound, from every initial probability measure. -/
theorem finiteDiscreteWalkLaw_ae_edge_jump_completion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (embedding : Vertex → Carrier) (jump : ℝ)
    (edgeBound : ∀ edge, dist (embedding (endpoint edge).1) (embedding (endpoint edge).2) ≤ jump) :
    ∀ᵐ path ∂finiteDiscreteWalkLaw endpoint positiveDegree initial,
      ∀ index, dist (embedding (path index)) (embedding (path (index + 1))) ≤ jump := by
  classical
  apply ae_all_iff.mpr
  intro index
  let law := finiteDiscreteWalkLaw endpoint positiveDegree initial
  let bad : Vertex → Vertex → ℝ := fun first last => if jump < dist (embedding first) (embedding last) then 1 else 0
  have pairIntegrable : Integrable (fun path => bad (path index) (path (index + 1))) law := by
    exact (show Integrable (Function.uncurry bad) (law.map (fun path => (path index, path (index + 1)))) from
      Integrable.of_finite).comp_aemeasurable
        ((measurable_pi_apply index).prodMk (measurable_pi_apply (index + 1))).aemeasurable
  have transitionZero (first : Vertex) : transition endpoint (bad first) first = 0 := by
    rw [transition_eq_kernel endpoint positiveDegree]
    apply Finset.sum_eq_zero
    intro last _
    by_cases far : jump < dist (embedding first) (embedding last)
    · rw [finiteTransitionKernel_zero_of_edge_jump_completion20261011 endpoint embedding jump edgeBound first last far]
      exact zero_mul _
    · simp only [bad, if_neg far, mul_zero]
  have integralZero : (∫ path, bad (path index) (path (index + 1)) ∂law) = 0 := by
    calc
      _ = ∫ path, (law[fun path => bad (path index) (path (index + 1)) | Filtration.piLE index]) path ∂law :=
        (integral_condExp (Filtration.piLE.le index)).symm
      _ = ∫ path, transition endpoint (bad (path index)) (path index) ∂law :=
        integral_congr_ae (finiteDiscreteWalkLaw_conditional_pair_expectation_completion20261011
          endpoint positiveDegree initial bad index)
      _ = 0 := by simp only [transitionZero, integral_zero]
  have zeroAE := (integral_eq_zero_iff_of_nonneg_ae
    (Eventually.of_forall fun path => by dsimp only [bad]; split_ifs <;> norm_num) pairIntegrable).mp integralZero
  filter_upwards [zeroAE] with path equality
  by_contra far
  have strict := not_le.mp far
  change (if jump < dist (embedding (path index)) (embedding (path (index + 1))) then (1 : ℝ) else 0) = 0 at equality
  rw [if_pos strict] at equality
  norm_num at equality

end
end IGSIII34.Diffusion
