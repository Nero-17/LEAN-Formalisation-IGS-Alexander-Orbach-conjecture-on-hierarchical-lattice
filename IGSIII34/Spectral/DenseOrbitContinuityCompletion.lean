import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Topology.MetricSpace.Pseudo.Defs

set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace IGSIII34.Spectral
noncomputable section
open Filter
open scoped Topology

variable {Parameter DenseCarrier Space : Type*} [TopologicalSpace Parameter]
  [NormedAddCommGroup Space] [NormedSpace ℝ Space]

theorem continuous_orbit_of_dense_continuous_orbits_completion
    (operators : Parameter → Space →L[ℝ] Space)
    (contractive : ∀ parameter value, ‖operators parameter value‖ ≤ ‖value‖)
    (embedding : DenseCarrier → Space) (dense : DenseRange embedding)
    (denseOrbits : ∀ value, Continuous (fun parameter => operators parameter (embedding value)))
    (value : Space) : Continuous (fun parameter => operators parameter value) := by
  apply continuous_iff_continuousAt.mpr
  intro parameter
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  obtain ⟨approximation, close⟩ := Metric.denseRange_iff.mp dense value (epsilon/3) (by positivity)
  have eventual : ∀ᶠ next in 𝓝 parameter,
      dist (operators next (embedding approximation)) (operators parameter (embedding approximation)) < epsilon/3 :=
    ((denseOrbits approximation).tendsto parameter).eventually (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [eventual] with next nearby
  have first : dist (operators next value) (operators next (embedding approximation)) ≤ dist value (embedding approximation) := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact contractive next _
  have last : dist (operators parameter (embedding approximation)) (operators parameter value) ≤ dist (embedding approximation) value := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact contractive parameter _
  have triangle := (dist_triangle (operators next value) (operators next (embedding approximation)) (operators parameter value)).trans
    (add_le_add le_rfl (dist_triangle (operators next (embedding approximation))
      (operators parameter (embedding approximation)) (operators parameter value)))
  rw [dist_comm (embedding approximation) value] at last
  linarith

end
end IGSIII34.Spectral
