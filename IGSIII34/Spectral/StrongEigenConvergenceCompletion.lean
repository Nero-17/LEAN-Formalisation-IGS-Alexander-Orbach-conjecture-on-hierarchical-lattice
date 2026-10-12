import IGSIII34.Spectral.DiagonalSemigroupCompletion

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open InnerProductSpace Filter
open scoped Topology NNReal

variable {Hilbert Index Parameter : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
  [CompleteSpace Hilbert]

theorem strong_convergence_of_basis_convergence_completion
    (basis : HilbertBasis Index ℝ Hilbert) (filter : Filter Parameter)
    (operators : Parameter → Hilbert →L[ℝ] Hilbert) (limit : Hilbert →L[ℝ] Hilbert)
    (contractive : ∀ parameter value, ‖operators parameter value‖ ≤ ‖value‖)
    (limitContractive : ∀ value, ‖limit value‖ ≤ ‖value‖)
    (basisConvergence : ∀ index, Tendsto (fun parameter => operators parameter (basis index)) filter (𝓝 (limit (basis index))))
    (value : Hilbert) : Tendsto (fun parameter => operators parameter value) filter (𝓝 (limit value)) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro epsilon positive
  have projectionClose : ∀ᶠ indices : Finset Index in atTop,
      dist (∑ index ∈ indices, basis.repr value index • basis index) value < epsilon / 3 := by
    simpa only [SummationFilter.unconditional_filter] using
      (basis.hasSum_repr value).eventually (Metric.ball_mem_nhds value (by linarith : 0 < epsilon / 3))
  obtain ⟨indices, close⟩ := projectionClose.exists
  let projection := ∑ index ∈ indices, basis.repr value index • basis index
  have projectionConvergence : Tendsto (fun parameter => operators parameter projection) filter (𝓝 (limit projection)) := by
    have convergence := tendsto_finsetSum indices (fun index _ => (basisConvergence index).const_smul (basis.repr value index))
    simpa only [projection, map_sum, map_smul] using convergence
  have eventual : ∀ᶠ parameter in filter, dist (operators parameter projection) (limit projection) < epsilon / 3 :=
    projectionConvergence.eventually (Metric.ball_mem_nhds _ (by linarith : 0 < epsilon / 3))
  filter_upwards [eventual] with parameter small
  have first : dist (operators parameter value) (operators parameter projection) ≤ dist value projection := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact contractive parameter _
  have last : dist (limit projection) (limit value) ≤ dist projection value := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact limitContractive _
  have triangle := (dist_triangle (operators parameter value) (operators parameter projection) (limit value)).trans
    (add_le_add le_rfl (dist_triangle (operators parameter projection) (limit projection) (limit value)))
  have closeOther : dist value projection < epsilon / 3 := by simpa only [dist_comm] using close
  linarith

end
end IGSIII34.Spectral
