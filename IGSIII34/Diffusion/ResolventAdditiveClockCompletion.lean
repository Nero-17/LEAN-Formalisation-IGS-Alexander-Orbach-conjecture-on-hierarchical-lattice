import IGSIII34.Diffusion.WalkNonstationaryQuadraticCompletion
import IGSIII34.Diffusion.FiniteResolventCompletion

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

def finiteWalkScaledAdditiveCompletion (clock : ℝ) (forcing : Vertex → ℝ) (time : ℕ) (path : ℕ → Vertex) : ℝ :=
  (∑ index ∈ Finset.range time, forcing (path index)) / clock

theorem finiteWalk_resolvent_additive_bound_completion
    (endpoint : Edge → Vertex × Vertex) (potential forcing : Vertex → ℝ)
    (parameter clock size horizon : ℝ) (parameterPositive : 0 < parameter) (clockPositive : 0 < clock)
    (sizeNonnegative : 0 ≤ size) (horizonNonnegative : 0 ≤ horizon)
    (equation : ∀ vertex, parameter * potential vertex - clock * rateOneGenerator endpoint potential vertex = forcing vertex)
    (potentialBound : ∀ vertex, |potential vertex| ≤ size)
    (time : ℕ) (timeBound : (time : ℝ) ≤ clock * horizon) (path : ℕ → Vertex) :
    |finiteWalkScaledAdditiveCompletion clock forcing time path| ≤
      (parameter * horizon + 2) * size + |walkCompensatedPotential endpoint potential time path| := by
  have sumEquation : (∑ index ∈ Finset.range time, forcing (path index)) =
      parameter * (∑ index ∈ Finset.range time, potential (path index)) -
        clock * (∑ index ∈ Finset.range time, rateOneGenerator endpoint potential (path index)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun index member => (equation (path index)).symm
  have sumPotentialBound : |∑ index ∈ Finset.range time, potential (path index)| ≤ time * size := by
    calc
      _ ≤ ∑ index ∈ Finset.range time, |potential (path index)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _index ∈ Finset.range time, size := Finset.sum_le_sum fun index member => potentialBound _
      _ = _ := by simp
  have scaledPotentialBound : |parameter / clock * (∑ index ∈ Finset.range time, potential (path index))| ≤ parameter * horizon * size := by
    rw [abs_mul, abs_of_nonneg (div_nonneg parameterPositive.le clockPositive.le)]
    have scaled := mul_le_mul_of_nonneg_left sumPotentialBound (div_nonneg parameterPositive.le clockPositive.le)
    have timeScaled : parameter / clock * (time * size) ≤ parameter * horizon * size := by
      have divided : (time : ℝ) / clock ≤ horizon := (div_le_iff₀ clockPositive).mpr (by simpa only [mul_comm] using timeBound)
      calc
        _ = ((time : ℝ) / clock) * (parameter * size) := by ring
        _ ≤ horizon * (parameter * size) := mul_le_mul_of_nonneg_right divided (mul_nonneg parameterPositive.le sizeNonnegative)
        _ = _ := by ring
    exact scaled.trans timeScaled
  have displacement : |potential (path time) - potential (path 0)| ≤ 2 * size :=
    (abs_sub _ _).trans (by linarith [potentialBound (path time), potentialBound (path 0)])
  have identity : finiteWalkScaledAdditiveCompletion clock forcing time path =
      parameter / clock * (∑ index ∈ Finset.range time, potential (path index)) -
        (potential (path time) - potential (path 0)) + walkCompensatedPotential endpoint potential time path := by
    unfold finiteWalkScaledAdditiveCompletion walkCompensatedPotential
    rw [sumEquation]
    field_simp
    <;> ring
  rw [identity]
  calc
    _ ≤ |parameter / clock * (∑ index ∈ Finset.range time, potential (path index)) -
        (potential (path time) - potential (path 0))| + |walkCompensatedPotential endpoint potential time path| := abs_add_le _ _
    _ ≤ (|parameter / clock * (∑ index ∈ Finset.range time, potential (path index))| +
        |potential (path time) - potential (path 0)|) + |walkCompensatedPotential endpoint potential time path| :=
      add_le_add_left (abs_sub _ _) _
    _ ≤ _ := by nlinarith

theorem finiteGraphResolvent_additive_maximal_bound_completion
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (parameter clock : ℝ) (parameterPositive : 0 < parameter) (clockPositive : 0 < clock)
    (forcing : Vertex → ℝ) (bound size horizon radius : ℝ)
    (boundNonnegative : 0 ≤ bound) (sizeNonnegative : 0 ≤ size) (horizonNonnegative : 0 ≤ horizon) (radiusPositive : 0 < radius)
    (forcingBound : ∀ vertex, |forcing vertex| ≤ bound)
    (potentialBound : ∀ vertex, |finiteGraphResolvent endpoint positiveDegree parameter clock parameterPositive clockPositive.le forcing vertex| ≤ size)
    (time : ℕ) (timeBound : (time : ℝ) ≤ clock * horizon)
    (small : (parameter * horizon + 2) * size ≤ radius / 2) :
    ENNReal.ofReal ((radius/2)^2) * (finiteDiscreteWalkLaw endpoint positiveDegree initial)
      {path | ∃ index ≤ time, radius ≤ |finiteWalkScaledAdditiveCompletion clock forcing index path|} ≤
      ENNReal.ofReal (size ^ 2 + 4 * horizon * size * bound) := by
  let potential := finiteGraphResolvent endpoint positiveDegree parameter clock parameterPositive clockPositive.le forcing
  have equation : ∀ vertex, parameter * potential vertex - clock * rateOneGenerator endpoint potential vertex = forcing vertex := by
    intro vertex
    have equationAt := congrFun (finiteGraphResolvent_equation endpoint positiveDegree parameter clock parameterPositive clockPositive.le forcing) vertex
    rw [finiteGraphResolventOperator_apply endpoint positiveDegree] at equationAt
    exact equationAt
  have generatorBound : ∀ vertex, |rateOneGenerator endpoint potential vertex| ≤ 2 * bound / clock := by
    intro vertex
    have bound := finiteGraphResolvent_generator_bound endpoint positiveDegree parameter clock parameterPositive clockPositive.le forcing bound forcingBound vertex
    rw [abs_mul, abs_of_pos clockPositive] at bound
    exact (le_div_iff₀ clockPositive).mpr (by nlinarith)
  have inclusion : {path : ℕ → Vertex | ∃ index ≤ time, radius ≤ |finiteWalkScaledAdditiveCompletion clock forcing index path|} ⊆
      {path | ∃ index ≤ time, radius / 2 ≤ |walkCompensatedPotential endpoint potential index path|} := by
    rintro path ⟨index, before, far⟩
    have indexBound : (index : ℝ) ≤ clock * horizon := (by exact_mod_cast before : (index : ℝ) ≤ time).trans timeBound
    have deterministic := finiteWalk_resolvent_additive_bound_completion endpoint potential forcing parameter clock size horizon
      parameterPositive clockPositive sizeNonnegative horizonNonnegative equation potentialBound index indexBound path
    exact ⟨index, before, by linarith⟩
  have variance := finiteWalk_compensated_square_bound_nonstationary_completion endpoint positiveDegree initial potential
    size (2 * bound / clock) sizeNonnegative (by positivity) potentialBound generatorBound time
  have arithmetic : size ^ 2 + 2 * time * size * (2 * bound / clock) ≤ size ^ 2 + 4 * horizon * size * bound := by
    have divided : (time : ℝ) / clock ≤ horizon := (div_le_iff₀ clockPositive).mpr (by simpa only [mul_comm] using timeBound)
    calc
      _ = size ^ 2 + ((time : ℝ) / clock) * (4 * size * bound) := by ring
      _ ≤ size ^ 2 + horizon * (4 * size * bound) := add_le_add_right (mul_le_mul_of_nonneg_right divided (by positivity)) _
      _ = _ := by ring
  exact (mul_le_mul_left' (measure_mono inclusion) _).trans
    ((finiteDiscreteWalkLaw_compensated_maximal_bound endpoint positiveDegree initial potential (radius/2) (by positivity) time).trans
      (ENNReal.ofReal_le_ofReal (variance.trans arithmetic)))

end
end IGSIII34.Diffusion



