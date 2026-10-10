import Mathlib.Topology.MetricSpace.GromovHausdorff

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace IGSIII.Geometry
noncomputable section

open Metric Set

/-- Matching actual finite anchors produces a genuine common metric,
preserving both original metrics and controlling Hausdorff and marked errors. -/
theorem exists_common_metric_of_anchor_distortion
    {Source Target Index : Type*} [MetricSpace Source] [MetricSpace Target] [Nonempty Index]
    (first : Index → Source) (second : Index → Target)
    (first_mesh second_mesh bridge : ℝ)
    (first_nonnegative : 0 ≤ first_mesh) (second_nonnegative : 0 ≤ second_mesh)
    (bridge_positive : 0 < bridge)
    (first_net : ∀ point : Source, ∃ index, dist point (first index) ≤ first_mesh)
    (second_net : ∀ point : Target, ∃ index, dist point (second index) ≤ second_mesh)
    (distortion : ∀ left right, |dist (first left) (first right) - dist (second left) (second right)| ≤ 2 * bridge) :
    ∃ common : MetricSpace (Source ⊕ Target),
      letI := common
      Isometry (@Sum.inl Source Target) ∧ Isometry (@Sum.inr Source Target) ∧
      (∀ index, dist (Sum.inl (first index)) (Sum.inr (second index)) = bridge) ∧
      hausdorffDist (Set.range (@Sum.inl Source Target)) (Set.range (@Sum.inr Source Target)) ≤
        first_mesh + bridge + second_mesh := by
  letI : MetricSpace (Source ⊕ Target) := glueMetricApprox first second bridge bridge_positive distortion
  have first_isometry : Isometry (@Sum.inl Source Target) := Isometry.of_dist_eq (fun _ _ => rfl)
  have second_isometry : Isometry (@Sum.inr Source Target) := Isometry.of_dist_eq (fun _ _ => rfl)
  have matched (index : Index) : dist (Sum.inl (first index)) (Sum.inr (second index)) = bridge :=
    glueDist_glued_points first second bridge index
  refine ⟨inferInstance, first_isometry, second_isometry, matched, ?_⟩
  apply hausdorffDist_le_of_mem_dist (by linarith)
  · rintro _ ⟨point, rfl⟩
    obtain ⟨index, close⟩ := first_net point
    refine ⟨Sum.inr (second index), ⟨second index, rfl⟩, ?_⟩
    have triangle := dist_triangle (Sum.inl point) (Sum.inl (first index)) (Sum.inr (second index))
    rw [first_isometry.dist_eq, matched] at triangle
    linarith
  · rintro _ ⟨point, rfl⟩
    obtain ⟨index, close⟩ := second_net point
    refine ⟨Sum.inl (first index), ⟨first index, rfl⟩, ?_⟩
    have triangle := dist_triangle (Sum.inr point) (Sum.inr (second index)) (Sum.inl (first index))
    rw [second_isometry.dist_eq, dist_comm (Sum.inr (second index)) (Sum.inl (first index)), matched] at triangle
    linarith

end
end IGSIII.Geometry
