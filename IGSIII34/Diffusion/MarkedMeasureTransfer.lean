import IGSIII.Geometry.MarkedGromovHausdorffProkhorov

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter IGSIII.Geometry
open scoped Topology

/-- Replacing the finite measure by one whose actual Prokhorov distance
vanishes preserves the entire marked Gromov--Hausdorff--Prokhorov limit. -/
theorem markedGHPConverges_of_measure_distance_tendsto_zero
    (Source : ℕ → Type*) [∀ depth, MetricSpace (Source depth)] [∀ depth, MeasurableSpace (Source depth)]
    [∀ depth, BorelSpace (Source depth)]
    {Target : Type*} [MetricSpace Target] [MeasurableSpace Target]
    (sourceMeasure otherMeasure : ∀ depth, Measure (Source depth)) (targetMeasure : Measure Target)
    (sourceMark : ∀ depth, Bool → Source depth) (targetMark : Bool → Target)
    (convergence : MarkedGHPConverges Source sourceMeasure targetMeasure sourceMark targetMark)
    (comparison : Tendsto (fun depth => levyProkhorovEDist (otherMeasure depth) (sourceMeasure depth)) atTop (𝓝 0)) :
    MarkedGHPConverges Source otherMeasure targetMeasure sourceMark targetMark := by
  intro epsilon epsilonPositive
  have small := (tendsto_order.mp comparison).2 (ENNReal.ofReal (epsilon / 2)) (by positivity)
  filter_upwards [convergence (epsilon / 2) (by positivity), small] with depth result small
  obtain ⟨common, firstIsometry, secondIsometry, hausdorff, measureBound, marks⟩ := result
  letI := common
  letI : TopologicalSpace (Source depth ⊕ Target) := common.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace (Source depth ⊕ Target) := borel (Source depth ⊕ Target)
  letI : BorelSpace (Source depth ⊕ Target) := ⟨rfl⟩
  refine ⟨common, firstIsometry, secondIsometry, hausdorff.trans (by linarith), ?_,
    fun side => (marks side).trans (by linarith)⟩
  have contraction := levyProkhorovEDist_map_le_of_lipschitz_one (otherMeasure depth) (sourceMeasure depth)
    (@Sum.inl (Source depth) Target) firstIsometry.lipschitz
  calc
    _ ≤ levyProkhorovEDist ((otherMeasure depth).map (@Sum.inl (Source depth) Target))
        ((sourceMeasure depth).map (@Sum.inl (Source depth) Target)) +
        levyProkhorovEDist ((sourceMeasure depth).map (@Sum.inl (Source depth) Target))
          (targetMeasure.map (@Sum.inr (Source depth) Target)) := levyProkhorovEDist_triangle _ _ _
    _ < ENNReal.ofReal (epsilon / 2) + ENNReal.ofReal (epsilon / 2) :=
      ENNReal.add_lt_add (contraction.trans_lt small) measureBound
    _ = ENNReal.ofReal epsilon := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end
end IGSIII34.Diffusion
