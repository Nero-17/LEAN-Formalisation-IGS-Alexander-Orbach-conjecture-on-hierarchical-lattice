import IGSIII34.Diffusion.FiniteVertexMeasureCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory IGSIII.Chemical.SmallBall
open scoped BigOperators
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Nonempty Vertex]
  [Fintype Edge] [Nonempty Edge]

def finiteCountingClockDensityCompletion20261011 (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) : ℝ :=
  (2 * Fintype.card Edge) / ((Fintype.card Vertex : ℝ) * degree endpoint vertex)

theorem finiteCountingClockDensity_weight_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (vertex : Vertex) :
    degreeWeight endpoint vertex * finiteCountingClockDensityCompletion20261011 endpoint vertex =
      1 / (Fintype.card Vertex : ℝ) := by
  unfold degreeWeight finiteCountingClockDensityCompletion20261011
  field_simp [(positiveDegree vertex).ne']

theorem finiteCountingClockDensity_integral_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (function : Vertex → ℝ) :
    (∫ vertex, finiteCountingClockDensityCompletion20261011 endpoint vertex * function vertex ∂degreeMeasure endpoint) =
      ∫ vertex, function vertex ∂uniformOn Set.univ := by
  rw [degreeMeasure_integral, finiteUniformMeasure_integral_completion20261011 endpoint]
  simp only [← mul_assoc, finiteCountingClockDensity_weight_completion20261011 endpoint positiveDegree]

theorem finiteCenteredCountingClock_integral_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (function : Vertex → ℝ) :
    (∫ vertex, (finiteCountingClockDensityCompletion20261011 endpoint vertex - 1) * function vertex ∂degreeMeasure endpoint) =
      (∫ vertex, function vertex ∂uniformOn Set.univ) - (∫ vertex, function vertex ∂degreeMeasure endpoint) := by
  simp only [sub_mul, one_mul]
  rw [integral_sub Integrable.of_finite Integrable.of_finite,
    finiteCountingClockDensity_integral_completion20261011 endpoint positiveDegree]

theorem finite_positive_degree_atLeastOne_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (vertex : Vertex) (positive : 0 < degree endpoint vertex) : 1 ≤ degree endpoint vertex := by
  have integerPositive : 0 < finiteDegreeNatCompletion20261011 endpoint vertex := by
    exact_mod_cast (show (0 : ℝ) < (finiteDegreeNatCompletion20261011 endpoint vertex : ℝ) by
      rw [finiteDegreeNat_cast_completion20261011]; exact positive)
  rw [← finiteDegreeNat_cast_completion20261011]
  exact_mod_cast integerPositive

theorem finiteCountingClockDensity_nonnegative_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (vertex : Vertex) : 0 ≤ finiteCountingClockDensityCompletion20261011 endpoint vertex := by
  unfold finiteCountingClockDensityCompletion20261011
  exact div_nonneg (by positivity) (mul_nonneg (by positivity) (degree_nonnegative endpoint vertex))

theorem finiteCountingClockDensity_upper_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (vertex : Vertex) (positive : 0 < degree endpoint vertex) :
    finiteCountingClockDensityCompletion20261011 endpoint vertex ≤
      (2 * Fintype.card Edge) / (Fintype.card Vertex : ℝ) := by
  unfold finiteCountingClockDensityCompletion20261011
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have lower := finite_positive_degree_atLeastOne_completion20261011 endpoint vertex positive
  nlinarith [show (0 : ℝ) ≤ Fintype.card Vertex by positivity]

theorem finiteCenteredCountingClock_bound_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (vertex : Vertex) :
    |finiteCountingClockDensityCompletion20261011 endpoint vertex - 1| ≤
      (2 * Fintype.card Edge) / (Fintype.card Vertex : ℝ) + 1 := by
  have nonnegative := finiteCountingClockDensity_nonnegative_completion20261011 endpoint vertex
  have upper := finiteCountingClockDensity_upper_completion20261011 endpoint vertex (positiveDegree vertex)
  calc
    _ ≤ |finiteCountingClockDensityCompletion20261011 endpoint vertex| + |(1 : ℝ)| := abs_sub _ _
    _ ≤ _ := by simpa only [abs_of_nonneg nonnegative, abs_one] using add_le_add_left upper 1

end
end IGSIII34.Diffusion

