import IGSIII34.Diffusion.FiniteVertexObjectiveCompletion20261011
import IGSIII.Geometry.ActualFiniteMass

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open Universality MeasureTheory ProbabilityTheory IGSIII.Chemical.SmallBall
open scoped BigOperators
variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Nonempty Vertex]
  [Fintype Edge] [Nonempty Edge]

theorem finiteRegularized_degreeMeasure_completion20261011 (endpoint : Edge → Vertex × Vertex) :
    degreeMeasure (finiteRegularizedEndpointCompletion20261011 endpoint) = uniformOn Set.univ := by
  apply Measure.ext_of_singleton
  intro vertex
  rw [degreeMeasure, finiteWeightPMF_singleton, finiteRegularized_degreeWeight_completion20261011,
    uniformOn_univ, Measure.count_singleton]
  simp only [ENNReal.ofReal_div_of_pos (Nat.cast_pos.mpr Fintype.card_pos), ENNReal.ofReal_one,
    ENNReal.ofReal_natCast]

theorem finiteUniformMeasure_integral_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (function : Vertex → ℝ) :
    (∫ vertex, function vertex ∂uniformOn Set.univ) =
      ∑ vertex, (1 / (Fintype.card Vertex : ℝ)) * function vertex := by
  rw [← finiteRegularized_degreeMeasure_completion20261011 endpoint, degreeMeasure_integral]
  simp only [finiteRegularized_degreeWeight_completion20261011]

theorem finiteVertexResolventFunctional_integral_completion20261011 (endpoint : Edge → Vertex × Vertex)
    (parameter scale : ℝ) (forcing potential : Vertex → ℝ) :
    finiteVertexResolventFunctionalCompletion20261011 endpoint parameter scale forcing potential =
      parameter * (∫ vertex, potential vertex ^ 2 ∂uniformOn Set.univ) + scale * energy endpoint potential -
        2 * (∫ vertex, forcing vertex * potential vertex ∂uniformOn Set.univ) := by
  rw [finiteUniformMeasure_integral_completion20261011 endpoint, finiteUniformMeasure_integral_completion20261011 endpoint]
  unfold finiteVertexResolventFunctionalCompletion20261011
  simp only [mul_assoc]

end
end IGSIII34.Diffusion

