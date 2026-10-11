import IGSIII34.Diffusion.FiniteResolventVariationalCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.Diffusion
noncomputable section
open scoped BigOperators

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex] [Fintype Edge]

def finiteResolventFunctionalCompletion20261011 (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (forcing potential : Vertex → ℝ) : ℝ :=
  parameter * (∑ vertex, degreeWeight endpoint vertex * potential vertex ^ 2) +
    scale * energy endpoint potential - 2 * ∑ vertex, degreeWeight endpoint vertex * forcing vertex * potential vertex

theorem finiteResolventFunctional_gap_completion20261011 [Nonempty Vertex] [Nonempty Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing test : Vertex → ℝ) :
    finiteResolventFunctionalCompletion20261011 endpoint parameter scale forcing test =
      finiteResolventFunctionalCompletion20261011 endpoint parameter scale forcing
        (finiteGraphResolvent endpoint positiveDegree parameter (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing) +
      parameter * ∑ vertex, degreeWeight endpoint vertex * (test vertex -
        finiteGraphResolvent endpoint positiveDegree parameter (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing vertex) ^ 2 +
      scale * energy endpoint (fun vertex => test vertex -
        finiteGraphResolvent endpoint positiveDegree parameter (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing vertex) := by
  let potential := finiteGraphResolvent endpoint positiveDegree parameter (2 * Fintype.card Edge * scale)
    parameterPositive (by positivity) forcing
  have energySplit : energy endpoint test = energy endpoint potential +
      2 * finiteMixedEnergyCompletion20261011 endpoint potential (fun vertex => test vertex - potential vertex) +
      energy endpoint (fun vertex => test vertex - potential vertex) := by
    unfold energy finiteMixedEnergyCompletion20261011
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro edge _
    ring
  have massSplit : (∑ vertex, degreeWeight endpoint vertex * test vertex ^ 2) =
      (∑ vertex, degreeWeight endpoint vertex * potential vertex ^ 2) +
      2 * (∑ vertex, degreeWeight endpoint vertex * potential vertex * (test vertex - potential vertex)) +
      ∑ vertex, degreeWeight endpoint vertex * (test vertex - potential vertex) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro vertex _
    ring
  have forcingSplit : (∑ vertex, degreeWeight endpoint vertex * forcing vertex * test vertex) =
      (∑ vertex, degreeWeight endpoint vertex * forcing vertex * potential vertex) +
      ∑ vertex, degreeWeight endpoint vertex * forcing vertex * (test vertex - potential vertex) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro vertex _
    ring
  have variation := finiteGraphResolvent_variational_completion20261011 endpoint positiveDegree parameter scale parameterPositive
    scaleNonnegative forcing (fun vertex => test vertex - potential vertex)
  change parameter * (∑ vertex, degreeWeight endpoint vertex * potential vertex * (test vertex - potential vertex)) +
    scale * finiteMixedEnergyCompletion20261011 endpoint potential (fun vertex => test vertex - potential vertex) =
    ∑ vertex, degreeWeight endpoint vertex * forcing vertex * (test vertex - potential vertex) at variation
  change finiteResolventFunctionalCompletion20261011 endpoint parameter scale forcing test =
    finiteResolventFunctionalCompletion20261011 endpoint parameter scale forcing potential +
    parameter * (∑ vertex, degreeWeight endpoint vertex * (test vertex - potential vertex) ^ 2) +
    scale * energy endpoint (fun vertex => test vertex - potential vertex)
  unfold finiteResolventFunctionalCompletion20261011
  rw [energySplit, massSplit, forcingSplit]
  nlinarith [variation]

/-- The constructed finite resolvent is a minimizer of the genuine
degree-mass plus full-edge Dirichlet functional against every finite test. -/
theorem finiteGraphResolvent_minimizes_completion20261011 [Nonempty Vertex] [Nonempty Edge]
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (parameter scale : ℝ) (parameterPositive : 0 < parameter) (scaleNonnegative : 0 ≤ scale)
    (forcing test : Vertex → ℝ) :
    finiteResolventFunctionalCompletion20261011 endpoint parameter scale forcing
      (finiteGraphResolvent endpoint positiveDegree parameter (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing) ≤
      finiteResolventFunctionalCompletion20261011 endpoint parameter scale forcing test := by
  rw [finiteResolventFunctional_gap_completion20261011 endpoint positiveDegree parameter scale parameterPositive scaleNonnegative forcing test]
  have massNonnegative : 0 ≤ ∑ vertex, degreeWeight endpoint vertex * (test vertex -
      finiteGraphResolvent endpoint positiveDegree parameter (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing vertex) ^ 2 :=
    Finset.sum_nonneg fun vertex _ => mul_nonneg (degreeWeight_nonnegative endpoint vertex) (sq_nonneg _)
  have energyNonnegative : 0 ≤ energy endpoint (fun vertex => test vertex -
      finiteGraphResolvent endpoint positiveDegree parameter (2 * Fintype.card Edge * scale) parameterPositive (by positivity) forcing vertex) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [mul_nonneg parameterPositive.le massNonnegative, mul_nonneg scaleNonnegative energyNonnegative]

end
end IGSIII34.Diffusion
