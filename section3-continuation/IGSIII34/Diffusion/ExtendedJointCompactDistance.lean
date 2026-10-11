import IGSIII34.Diffusion.ExtendedJointCompactCouplingGlue
import IGSIII34.Diffusion.OriginalJointCompactDistance
import Mathlib.Topology.MetricSpace.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Set TopologicalSpace MeasureTheory Filter Metric
open scoped Topology BigOperators ENNReal

def extendedJointCompactDistance
    (first last : ExtendedJointCompactRepresentative) : ℝ :=
  sInf (range (fun coupling : ExtendedJointCompactCoupling first last => coupling.cost))

theorem extendedJointCompactDistance_bddBelow
    (first last : ExtendedJointCompactRepresentative) :
    BddBelow (range (fun coupling : ExtendedJointCompactCoupling first last => coupling.cost)) :=
  ⟨0, by rintro _ ⟨coupling, rfl⟩; exact coupling.cost_nonnegative⟩

theorem extendedJointCompactDistance_range_nonempty
    (first last : ExtendedJointCompactRepresentative) :
    (range (fun coupling : ExtendedJointCompactCoupling first last => coupling.cost)).Nonempty := by
  obtain ⟨coupling⟩ := ExtendedJointCompactCoupling.exists first last
  exact ⟨coupling.cost, ⟨coupling, rfl⟩⟩

theorem extendedJointCompactDistance_nonnegative
    (first last : ExtendedJointCompactRepresentative) :
    0 ≤ extendedJointCompactDistance first last := by
  apply le_csInf (extendedJointCompactDistance_range_nonempty first last)
  rintro _ ⟨coupling, rfl⟩
  exact coupling.cost_nonnegative

theorem extendedJointCompactDistance_le_cost
    {first last : ExtendedJointCompactRepresentative}
    (coupling : ExtendedJointCompactCoupling first last) :
    extendedJointCompactDistance first last ≤ coupling.cost :=
  csInf_le (extendedJointCompactDistance_bddBelow first last) ⟨coupling, rfl⟩

theorem extendedJointCompactDistance_self
    (representative : ExtendedJointCompactRepresentative) :
    extendedJointCompactDistance representative representative = 0 := by
  apply le_antisymm
  · exact (extendedJointCompactDistance_le_cost
      (ExtendedJointCompactCoupling.reflexive representative)).trans_eq
      (ExtendedJointCompactCoupling.cost_reflexive representative)
  · exact extendedJointCompactDistance_nonnegative _ _

theorem extendedJointCompactDistance_comm
    (first last : ExtendedJointCompactRepresentative) :
    extendedJointCompactDistance first last = extendedJointCompactDistance last first := by
  have bound (first last : ExtendedJointCompactRepresentative) :
      extendedJointCompactDistance first last ≤ extendedJointCompactDistance last first := by
    apply le_csInf (extendedJointCompactDistance_range_nonempty last first)
    rintro _ ⟨coupling, rfl⟩
    exact (extendedJointCompactDistance_le_cost coupling.reverse).trans_eq coupling.cost_reverse
  exact (bound first last).antisymm (bound last first)

theorem extendedJointCompactDistance_lt_iff
    (first last : ExtendedJointCompactRepresentative) (tolerance : ℝ) :
    extendedJointCompactDistance first last < tolerance ↔
      ∃ coupling : ExtendedJointCompactCoupling first last, coupling.cost < tolerance := by
  rw [extendedJointCompactDistance,
    csInf_lt_iff (extendedJointCompactDistance_bddBelow first last)
      (extendedJointCompactDistance_range_nonempty first last)]
  constructor
  · rintro ⟨_, ⟨coupling, rfl⟩, bound⟩
    exact ⟨coupling, bound⟩
  · rintro ⟨coupling, bound⟩
    exact ⟨coupling.cost, ⟨coupling, rfl⟩, bound⟩


theorem extendedJointCompactDistance_triangle
    (first middle last : ExtendedJointCompactRepresentative) :
    extendedJointCompactDistance first last ≤ extendedJointCompactDistance first middle +
      extendedJointCompactDistance middle last := by
  apply le_of_forall_pos_le_add
  intro tolerance positive
  obtain ⟨left, leftBound⟩ := (extendedJointCompactDistance_lt_iff first middle
    (extendedJointCompactDistance first middle + tolerance / 2)).mp (by linarith)
  obtain ⟨right, rightBound⟩ := (extendedJointCompactDistance_lt_iff middle last
    (extendedJointCompactDistance middle last + tolerance / 2)).mp (by linarith)
  have upper := (extendedJointCompactDistance_le_cost (left.glue right)).trans
    (left.glue_cost_le right)
  linarith

instance extendedJointCompactRepresentativePseudoMetric :
    PseudoMetricSpace ExtendedJointCompactRepresentative where
  dist := extendedJointCompactDistance
  dist_self := extendedJointCompactDistance_self
  dist_comm := extendedJointCompactDistance_comm
  dist_triangle := extendedJointCompactDistance_triangle

/-- The metric separation of the genuine original common-isometric-embedding
distance. Whole paths are compared in integer-horizon J1; the usual-local
continuous-limit transfer is a separate obligation. -/
def ExtendedJointCompactSpace := SeparationQuotient ExtendedJointCompactRepresentative

instance : MetricSpace ExtendedJointCompactSpace :=
  inferInstanceAs (MetricSpace (SeparationQuotient ExtendedJointCompactRepresentative))
instance : MeasurableSpace ExtendedJointCompactSpace := borel _
instance : BorelSpace ExtendedJointCompactSpace := ⟨rfl⟩

def extendedJointCompactClass (representative : ExtendedJointCompactRepresentative) :
    ExtendedJointCompactSpace := SeparationQuotient.mk representative

theorem extendedJointCompactClass_dist
    (first last : ExtendedJointCompactRepresentative) :
    dist (extendedJointCompactClass first) (extendedJointCompactClass last) =
      extendedJointCompactDistance first last := rfl

/-- This equivalence links metric convergence to actual common compact
isometric couplings controlling all spatial data and the entire path.
It is not merely convergence of coordinate observations. -/
theorem extendedJointCompactClass_tendsto_iff
    (sequence : ℕ → ExtendedJointCompactRepresentative)
    (target : ExtendedJointCompactRepresentative) :
    Tendsto (fun depth => extendedJointCompactClass (sequence depth)) atTop
      (𝓝 (extendedJointCompactClass target)) ↔
    ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop,
      ∃ coupling : ExtendedJointCompactCoupling (sequence depth) target,
        coupling.cost < tolerance := by
  rw [Metric.tendsto_nhds]
  simp_rw [extendedJointCompactClass_dist,
    extendedJointCompactDistance_lt_iff]


theorem extendedJointCompactDistance_ofOriginal
    (first last : OriginalJointCompactRepresentative) :
    extendedJointCompactDistance (.ofOriginal first) (.ofOriginal last) =
      originalJointCompactDistance first last := by
  apply le_antisymm
  · apply le_csInf (originalJointCompactDistance_range_nonempty first last)
    rintro _ ⟨coupling, rfl⟩
    exact extendedJointCompactDistance_le_cost coupling.toExtended
  · apply le_csInf (extendedJointCompactDistance_range_nonempty _ _)
    rintro _ ⟨coupling, rfl⟩
    exact originalJointCompactDistance_le_cost coupling.toOriginal

end
end IGSIII34.Diffusion
