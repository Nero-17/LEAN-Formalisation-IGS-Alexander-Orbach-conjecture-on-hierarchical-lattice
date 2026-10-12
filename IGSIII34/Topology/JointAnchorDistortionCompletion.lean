import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace IGSIII34.Topology
noncomputable section

/-- Coupled nets control the distortion of the full projection, not
merely the distortion on a finite collection of anchors. -/
theorem joint_anchor_projection_distortion_completion
    {Source Target Anchor : Type*} [PseudoMetricSpace Source] [PseudoMetricSpace Target]
    (sourceAnchor : Anchor → Source) (targetAnchor : Anchor → Target) (projection : Source → Target)
    (sourceMesh targetMesh error : ℝ)
    (jointNet : ∀ point, ∃ anchor, dist point (sourceAnchor anchor) ≤ sourceMesh ∧
      dist (projection point) (targetAnchor anchor) ≤ targetMesh)
    (anchorDistortion : ∀ first last,
      |dist (sourceAnchor first) (sourceAnchor last) - dist (targetAnchor first) (targetAnchor last)| ≤ error)
    (first last : Source) :
    |dist first last - dist (projection first) (projection last)| ≤ 2*sourceMesh+2*targetMesh+error := by
  obtain ⟨firstAnchor, sourceFirst, targetFirst⟩ := jointNet first
  obtain ⟨lastAnchor, sourceLast, targetLast⟩ := jointNet last
  have forwardSource : dist first last ≤ sourceMesh+
      dist (sourceAnchor firstAnchor) (sourceAnchor lastAnchor)+sourceMesh := by
    calc
      dist first last ≤ dist first (sourceAnchor firstAnchor)+
          (dist (sourceAnchor firstAnchor) (sourceAnchor lastAnchor)+dist (sourceAnchor lastAnchor) last) :=
        (dist_triangle _ _ _).trans (add_le_add (le_refl _) (dist_triangle _ _ _))
      _ ≤ sourceMesh+(dist (sourceAnchor firstAnchor) (sourceAnchor lastAnchor)+sourceMesh) := by
        rw [dist_comm (sourceAnchor lastAnchor) last]
        exact add_le_add sourceFirst (add_le_add (le_refl _) sourceLast)
      _ = _ := by ring
  have backwardSource : dist (sourceAnchor firstAnchor) (sourceAnchor lastAnchor) ≤ sourceMesh+dist first last+sourceMesh := by
    have triangle := (dist_triangle (sourceAnchor firstAnchor) first (sourceAnchor lastAnchor)).trans
      (add_le_add (le_refl _) (dist_triangle first last (sourceAnchor lastAnchor)))
    rw [dist_comm (sourceAnchor firstAnchor) first] at triangle
    linarith
  have forwardTarget : dist (projection first) (projection last) ≤ targetMesh+
      dist (targetAnchor firstAnchor) (targetAnchor lastAnchor)+targetMesh := by
    have triangle := (dist_triangle (projection first) (targetAnchor firstAnchor) (projection last)).trans
      (add_le_add (le_refl _) (dist_triangle (targetAnchor firstAnchor) (targetAnchor lastAnchor) (projection last)))
    rw [dist_comm (targetAnchor lastAnchor) (projection last)] at triangle
    linarith
  have backwardTarget : dist (targetAnchor firstAnchor) (targetAnchor lastAnchor) ≤ targetMesh+
      dist (projection first) (projection last)+targetMesh := by
    have triangle := (dist_triangle (targetAnchor firstAnchor) (projection first) (targetAnchor lastAnchor)).trans
      (add_le_add (le_refl _) (dist_triangle (projection first) (projection last) (targetAnchor lastAnchor)))
    rw [dist_comm (targetAnchor firstAnchor) (projection first)] at triangle
    linarith
  have distortion := abs_le.mp (anchorDistortion firstAnchor lastAnchor)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end
end IGSIII34.Topology
