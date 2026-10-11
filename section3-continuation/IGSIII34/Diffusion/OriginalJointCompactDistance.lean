import IGSIII34.Diffusion.OriginalJointCompactDistanceBasic
import IGSIII34.Diffusion.OriginalJointCompactCouplingGlue
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Filter TopologicalSpace
open scoped Topology

theorem originalJointCompactDistance_triangle
    (first middle last : OriginalJointCompactRepresentative) :
    originalJointCompactDistance first last ≤ originalJointCompactDistance first middle +
      originalJointCompactDistance middle last := by
  apply le_of_forall_pos_le_add
  intro tolerance positive
  obtain ⟨left, leftBound⟩ := (originalJointCompactDistance_lt_iff first middle
    (originalJointCompactDistance first middle + tolerance / 2)).mp (by linarith)
  obtain ⟨right, rightBound⟩ := (originalJointCompactDistance_lt_iff middle last
    (originalJointCompactDistance middle last + tolerance / 2)).mp (by linarith)
  have upper := (originalJointCompactDistance_le_cost (left.glue right)).trans
    (left.glue_cost_le right)
  linarith

instance originalJointCompactRepresentativePseudoMetric :
    PseudoMetricSpace OriginalJointCompactRepresentative where
  dist := originalJointCompactDistance
  dist_self := originalJointCompactDistance_self
  dist_comm := originalJointCompactDistance_comm
  dist_triangle := originalJointCompactDistance_triangle

/-- The metric separation of the genuine original common-isometric-embedding
distance. Whole paths are compared in integer-horizon J1; the usual-local
continuous-limit transfer is a separate obligation. -/
def OriginalJointCompactSpace := SeparationQuotient OriginalJointCompactRepresentative

instance : MetricSpace OriginalJointCompactSpace :=
  inferInstanceAs (MetricSpace (SeparationQuotient OriginalJointCompactRepresentative))
instance : MeasurableSpace OriginalJointCompactSpace := borel _
instance : BorelSpace OriginalJointCompactSpace := ⟨rfl⟩

def originalJointCompactClass (representative : OriginalJointCompactRepresentative) :
    OriginalJointCompactSpace := SeparationQuotient.mk representative

theorem originalJointCompactClass_dist
    (first last : OriginalJointCompactRepresentative) :
    dist (originalJointCompactClass first) (originalJointCompactClass last) =
      originalJointCompactDistance first last := rfl

/-- This equivalence links metric convergence to actual common compact
isometric couplings controlling all spatial data and the entire path.
It is not merely convergence of coordinate observations. -/
theorem originalJointCompactClass_tendsto_iff
    (sequence : ℕ → OriginalJointCompactRepresentative)
    (target : OriginalJointCompactRepresentative) :
    Tendsto (fun depth => originalJointCompactClass (sequence depth)) atTop
      (𝓝 (originalJointCompactClass target)) ↔
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∃ coupling : OriginalJointCompactCoupling (sequence depth) target,
        coupling.cost < tolerance := by
  rw [Metric.tendsto_nhds]
  simp_rw [originalJointCompactClass_dist,
    originalJointCompactDistance_lt_iff]

end
end IGSIII34.Diffusion
