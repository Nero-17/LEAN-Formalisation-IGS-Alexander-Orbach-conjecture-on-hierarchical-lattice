import IGSIII.Geometry.GeometricBoundaryRealization
import Mathlib.MeasureTheory.Measure.Support

set_option autoImplicit false
set_option maxHeartbeats 600000

namespace IGSIII.Geometry
noncomputable section

open MeasureTheory Filter
open scoped Topology

/-- Positive finite cylinders near every point force full support of the
constructed boundary pushforward. Only the proved metric tail bound is used. -/
theorem boundary_pushforward_full_support
    {Alphabet Space : Type*} [MeasurableSpace Alphabet] [MetricSpace Space]
    [MeasurableSpace Space] [BorelSpace Space]
    (boundary : Measure (Π depth, Fin depth → Alphabet))
    (weight : (depth : ℕ) → (Fin depth → Alphabet) → ℝ)
    (atoms : ∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight depth word))
    (index : ℕ → ℕ) (anchor : (depth : ℕ) → (Fin (index depth) → Alphabet) → Space)
    (realization : (Π depth, Fin depth → Alphabet) → Space) (measurable : Measurable realization)
    (mesh : ℕ → ℝ) (vanishing : Tendsto mesh atTop (𝓝 0))
    (close : ∀ depth, ∀ᵐ path ∂boundary, dist (anchor depth (path (index depth))) (realization path) ≤ mesh depth)
    (positive_anchors : ∀ point : Space, ∀ radius : ℝ, 0 < radius → ∀ start : ℕ,
      ∃ depth, start ≤ depth ∧ ∃ word : Fin (index depth) → Alphabet,
        0 < weight (index depth) word ∧ dist point (anchor depth word) < radius) :
    (boundary.map realization).IsOpenPosMeasure ∧ (boundary.map realization).support = Set.univ := by
  have positive_ball (point : Space) (radius : ℝ) (radius_positive : 0 < radius) :
      0 < boundary.map realization (Metric.ball point radius) := by
    have mesh_small := (tendsto_order.mp vanishing).2 (radius / 2) (by linarith)
    obtain ⟨start, mesh_small⟩ := eventually_atTop.mp mesh_small
    obtain ⟨depth, beyond, word, word_positive, anchor_close⟩ :=
      positive_anchors point (radius / 2) (by linarith) start
    have cylinder_positive : 0 < boundary {path | path (index depth) = word} := by
      rw [atoms]
      exact ENNReal.ofReal_pos.mpr word_positive
    apply cylinder_positive.trans_le
    rw [Measure.map_apply measurable Metric.isOpen_ball.measurableSet]
    apply measure_mono_ae
    filter_upwards [close depth] with path estimate
    intro belongs
    have identity : path (index depth) = word := belongs
    rw [identity] at estimate
    change dist (realization path) point < radius
    exact (dist_triangle (realization path) (anchor depth word) point).trans_lt (by
      rw [dist_comm (realization path) (anchor depth word), dist_comm (anchor depth word) point]
      linarith [mesh_small depth beyond])
  have full : (boundary.map realization).IsOpenPosMeasure := by
    constructor
    intro event opened nonempty
    obtain ⟨point, belongs⟩ := nonempty
    obtain ⟨radius, radius_positive, contained⟩ := Metric.isOpen_iff.mp opened point belongs
    exact ne_of_gt ((positive_ball point radius radius_positive).trans_le (measure_mono contained))
  letI := full
  exact ⟨full, Measure.support_eq_univ⟩

end
end IGSIII.Geometry
