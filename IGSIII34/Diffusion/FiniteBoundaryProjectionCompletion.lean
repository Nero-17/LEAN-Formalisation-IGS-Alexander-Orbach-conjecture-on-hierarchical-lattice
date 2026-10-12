import IGSIII.Geometry.FullComponentMassApproximation
set_option autoImplicit false
namespace IGSIII34.Diffusion
noncomputable section
open Universality IGSIII.Geometry MeasureTheory Filter
open scoped BigOperators _root_.Topology

theorem finite_boundary_projection_tendsto_completion
    {Alphabet Space : Type*} [Fintype Alphabet] [MeasurableSpace Alphabet] [MeasurableSingletonClass Alphabet]
    [MetricSpace Space] [MeasurableSpace Space] [BorelSpace Space]
    (measures : ℕ → Measure Alphabet)
    (weights : ℕ → Alphabet → ℝ) (nonnegative : ∀ index point, 0 ≤ weights index point)
    (massOne : ∀ index, ∑ point, weights index point = 1)
    (measuresEqual : ∀ index, measures index = (finiteWeightPMF (weights index) (nonnegative index) (massOne index)).toMeasure)
    (limitWeights : Alphabet → ℝ) (limitNonnegative : ∀ point, 0 ≤ limitWeights point)
    (limitMassOne : ∑ point, limitWeights point = 1)
    (convergence : ∀ point, Tendsto (fun index => weights index point) atTop (𝓝 (limitWeights point)))
    (limitLaw : Measure Alphabet) (atoms : ∀ point, limitLaw {point} = ENNReal.ofReal (limitWeights point))
    (anchor : Alphabet → Space) :
    Tendsto (fun index => levyProkhorovEDist ((measures index).map anchor) (limitLaw.map anchor)) atTop (𝓝 0) := by
  have lawEqual : limitLaw = (finiteWeightPMF limitWeights limitNonnegative limitMassOne).toMeasure := by
    apply Measure.ext_of_singleton
    intro point
    rw [finiteWeightPMF_singleton]
    exact atoms point
  have limit := levyProkhorovEDist_finiteWeightPMF_map_tendsto_zero weights limitWeights nonnegative limitNonnegative
    massOne limitMassOne convergence anchor (measurable_of_finite _)
  simpa only [← measuresEqual, ← lawEqual] using limit

end
end IGSIII34.Diffusion
