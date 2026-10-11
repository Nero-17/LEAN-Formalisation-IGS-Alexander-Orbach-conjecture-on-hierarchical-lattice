import IGSIII34.Diffusion.WalkQuadraticVariationCompletion20261011
import IGSIII34.Diffusion.SpectralCorrectorGeneratorCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped _root_.Topology
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [StandardBorelSpace Vertex] [Nonempty Vertex]

theorem finite_walk_paired_transition_completion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (potential : Vertex → ℝ) (time : ℕ) (past : (ℕ → Vertex) → ℝ)
    (pastKnown : StronglyMeasurable[Filtration.piLE time] past)
    (pastSquareIntegrable : MemLp past 2 (finiteDiscreteWalkLaw endpoint positiveDegree initial)) :
    (∫ path, past path * potential (path (time + 1)) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
      ∫ path, past path * transition endpoint potential (path time) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial := by
  let law := finiteDiscreteWalkLaw endpoint positiveDegree initial
  have nextSquareIntegrable := finitePathPotential_memLp_completion20261011 law potential (time + 1) 2
  have transitionSquareIntegrable := finitePathPotential_memLp_completion20261011 law (transition endpoint potential) time 2
  have zero := squareIntegrable_past_zeroMean_product_completion20261011 law (Filtration.piLE time) (Filtration.piLE.le time)
    past (fun path => potential (path (time + 1)) - transition endpoint potential (path time)) pastKnown pastSquareIntegrable
    (nextSquareIntegrable.sub transitionSquareIntegrable)
    (walkCompensatedPotential_increment_mean_zero_completion20261011 endpoint positiveDegree initial potential time)
  have nextProduct : Integrable (fun path => past path * potential (path (time + 1))) law :=
    memLp_one_iff_integrable.mp (nextSquareIntegrable.mul pastSquareIntegrable)
  have transitionProduct : Integrable (fun path => past path * transition endpoint potential (path time)) law :=
    memLp_one_iff_integrable.mp (transitionSquareIntegrable.mul pastSquareIntegrable)
  have productSplit : (fun path => past path * (potential (path (time + 1)) - transition endpoint potential (path time))) =
      (fun path => past path * potential (path (time + 1))) - (fun path => past path * transition endpoint potential (path time)) := by
    funext path
    simp only [Pi.sub_apply]
    ring
  rw [productSplit] at zero
  change (∫ path, past path * potential (path (time + 1)) - past path * transition endpoint potential (path time) ∂law) = 0 at zero
  rw [integral_sub nextProduct transitionProduct] at zero
  exact sub_eq_zero.mp zero

/-- The genuine full-past walk conditional law gives the scalar perturbed
Euler recurrence. Its error is the actual graph-generator error. -/
theorem finite_walk_paired_euler_completion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (potential error : Vertex → ℝ) (acceleration eigenvalue : ℝ) (accelerationPositive : 0 < acceleration)
    (generator : ∀ vertex, acceleration * rateOneGenerator endpoint potential vertex = -eigenvalue * potential vertex + error vertex)
    (time : ℕ) (past : (ℕ → Vertex) → ℝ)
    (pastKnown : StronglyMeasurable[Filtration.piLE time] past)
    (pastSquareIntegrable : MemLp past 2 (finiteDiscreteWalkLaw endpoint positiveDegree initial)) :
    (∫ path, past path * potential (path (time + 1)) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) =
      (1 - eigenvalue / acceleration) * (∫ path, past path * potential (path time) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) +
      (∫ path, past path * error (path time) ∂finiteDiscreteWalkLaw endpoint positiveDegree initial) / acceleration := by
  let law := finiteDiscreteWalkLaw endpoint positiveDegree initial
  have transitionIdentity (vertex : Vertex) : transition endpoint potential vertex =
      (1 - eigenvalue / acceleration) * potential vertex + error vertex / acceleration := by
    have equation := generator vertex
    rw [← transition_sub_identity] at equation
    apply (mul_left_cancel₀ accelerationPositive.ne')
    field_simp
    nlinarith [equation]
  rw [finite_walk_paired_transition_completion20261011 endpoint positiveDegree initial potential time past pastKnown pastSquareIntegrable]
  have potentialProduct : Integrable (fun path => past path * potential (path time)) law :=
    memLp_one_iff_integrable.mp ((finitePathPotential_memLp_completion20261011 law potential time 2).mul pastSquareIntegrable)
  have errorProduct : Integrable (fun path => past path * error (path time)) law :=
    memLp_one_iff_integrable.mp ((finitePathPotential_memLp_completion20261011 law error time 2).mul pastSquareIntegrable)
  have integrandIdentity : (fun path => past path * transition endpoint potential (path time)) =
      (fun path => (1 - eigenvalue / acceleration) * (past path * potential (path time))) +
        (fun path => (past path * error (path time)) / acceleration) := by
    funext path
    simp only [Pi.add_apply]
    rw [transitionIdentity]
    ring
  rw [integrandIdentity]
  change (∫ path, (1 - eigenvalue / acceleration) * (past path * potential (path time)) +
    (past path * error (path time)) / acceleration ∂law) = _
  rw [integral_add (potentialProduct.const_mul _) (errorProduct.div_const _), integral_const_mul, integral_div]

end
end IGSIII34.Diffusion


