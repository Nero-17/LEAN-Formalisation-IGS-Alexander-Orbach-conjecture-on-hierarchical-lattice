import IGSIII34.Diffusion.FiniteVertexMeasureCompletion

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory ProbabilityTheory IGSIII.Chemical.SmallBall
open scoped BigOperators
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Nonempty Vertex]
  [Fintype Edge] [Nonempty Edge]

def finiteCountingClockDensityCompletion (endpoint : Edge → Vertex × Vertex) (vertex : Vertex) : ℝ :=
  (2 * Fintype.card Edge) / ((Fintype.card Vertex : ℝ) * degree endpoint vertex)

theorem finiteCountingClockDensity_weight_completion (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (vertex : Vertex) :
    degreeWeight endpoint vertex * finiteCountingClockDensityCompletion endpoint vertex =
      1 / (Fintype.card Vertex : ℝ) := by
  unfold degreeWeight finiteCountingClockDensityCompletion
  field_simp [(positiveDegree vertex).ne']

theorem finiteCountingClockDensity_integral_completion (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (function : Vertex → ℝ) :
    (∫ vertex, finiteCountingClockDensityCompletion endpoint vertex * function vertex ∂degreeMeasure endpoint) =
      ∫ vertex, function vertex ∂uniformOn Set.univ := by
  rw [degreeMeasure_integral, finiteUniformMeasure_integral_completion endpoint]
  simp only [← mul_assoc, finiteCountingClockDensity_weight_completion endpoint positiveDegree]

theorem finiteCenteredCountingClock_integral_completion (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (function : Vertex → ℝ) :
    (∫ vertex, (finiteCountingClockDensityCompletion endpoint vertex - 1) * function vertex ∂degreeMeasure endpoint) =
      (∫ vertex, function vertex ∂uniformOn Set.univ) - (∫ vertex, function vertex ∂degreeMeasure endpoint) := by
  simp only [sub_mul, one_mul]
  rw [integral_sub Integrable.of_finite Integrable.of_finite,
    finiteCountingClockDensity_integral_completion endpoint positiveDegree]

theorem finite_positive_degree_atLeastOne_completion (endpoint : Edge → Vertex × Vertex)
    (vertex : Vertex) (positive : 0 < degree endpoint vertex) : 1 ≤ degree endpoint vertex := by
  have integerPositive : 0 < finiteDegreeNatCompletion endpoint vertex := by
    exact_mod_cast (show (0 : ℝ) < (finiteDegreeNatCompletion endpoint vertex : ℝ) by
      rw [finiteDegreeNat_cast_completion]; exact positive)
  rw [← finiteDegreeNat_cast_completion]
  exact_mod_cast integerPositive

theorem finiteCountingClockDensity_nonnegative_completion (endpoint : Edge → Vertex × Vertex)
    (vertex : Vertex) : 0 ≤ finiteCountingClockDensityCompletion endpoint vertex := by
  unfold finiteCountingClockDensityCompletion
  exact div_nonneg (by positivity) (mul_nonneg (by positivity) (degree_nonnegative endpoint vertex))

theorem finiteCountingClockDensity_upper_completion (endpoint : Edge → Vertex × Vertex)
    (vertex : Vertex) (positive : 0 < degree endpoint vertex) :
    finiteCountingClockDensityCompletion endpoint vertex ≤
      (2 * Fintype.card Edge) / (Fintype.card Vertex : ℝ) := by
  unfold finiteCountingClockDensityCompletion
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have lower := finite_positive_degree_atLeastOne_completion endpoint vertex positive
  nlinarith [show (0 : ℝ) ≤ Fintype.card Vertex by positivity]

theorem finiteCenteredCountingClock_bound_completion (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) (vertex : Vertex) :
    |finiteCountingClockDensityCompletion endpoint vertex - 1| ≤
      (2 * Fintype.card Edge) / (Fintype.card Vertex : ℝ) + 1 := by
  have nonnegative := finiteCountingClockDensity_nonnegative_completion endpoint vertex
  have upper := finiteCountingClockDensity_upper_completion endpoint vertex (positiveDegree vertex)
  calc
    _ ≤ |finiteCountingClockDensityCompletion endpoint vertex| + |(1 : ℝ)| := abs_sub _ _
    _ ≤ _ := by simpa only [abs_of_nonneg nonnegative, abs_one] using add_le_add_left upper 1

end
end IGSIII34.Diffusion

