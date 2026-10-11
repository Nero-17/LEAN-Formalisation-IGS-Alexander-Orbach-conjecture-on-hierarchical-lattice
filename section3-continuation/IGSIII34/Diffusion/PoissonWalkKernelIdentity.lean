import IGSIII34.Diffusion.PoissonWalkSemigroup

set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory

theorem poissonMeasure_zero_eq_dirac : poissonMeasure 0 = Measure.dirac 0 := by
  apply Measure.ext_of_singleton
  intro count
  rw [poissonMeasure_singleton]
  cases count with
  | zero => simp
  | succ count => simp

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

/-- The genuinely constructed Poisson transition semigroup begins at the
identity kernel, so its Chapman--Kolmogorov law includes time zero. -/
theorem poissonWalkKernel_zero (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex) :
    poissonWalkKernel endpoint positiveDegree 0 = Kernel.id := by
  ext first : 1
  rw [poissonWalkKernel_apply, poissonMeasure_zero_eq_dirac,
    Measure.dirac_bind (measurable_of_countable _), pow_zero]
  rfl

end
end IGSIII34.Diffusion
