import IGSIII34.Diffusion.WholeCadlagIsometricTransport
import IGSIII34.Diffusion.CompactIsometricGluing
import IGSIII34.Diffusion.IntrinsicJointGHPPathTest

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

def OriginalJointUniversalSpace := lp (fun _ : ℕ => ℝ) ∞
instance : MetricSpace OriginalJointUniversalSpace := inferInstanceAs (MetricSpace (lp (fun _ : ℕ => ℝ) ∞))
instance : MeasurableSpace OriginalJointUniversalSpace := borel _
instance : BorelSpace OriginalJointUniversalSpace := ⟨rfl⟩

/-- A representative retains the original metric and keeps the planted
marks, physical masses, and entire cadlag path inside its compact carrier. -/
structure OriginalJointCompactRepresentative where
  carrier : NonemptyCompacts OriginalJointUniversalSpace
  marks : Bool → carrier
  masses : Bool → ProbabilityMeasure carrier
  path : SkorokhodCadlagPathCompletion20261011 carrier

/-- A coupling consists of true isometric placements into one compact
ambient. No distance-profile homeomorphism is substituted for an isometry. -/
structure OriginalJointCompactCoupling
    (first last : OriginalJointCompactRepresentative) where
  ambient : NonemptyCompacts OriginalJointUniversalSpace
  firstPlacement : first.carrier → ambient
  firstIsometry : Isometry firstPlacement
  lastPlacement : last.carrier → ambient
  lastIsometry : Isometry lastPlacement

def originalJointRepresentativeState (representative : OriginalJointCompactRepresentative) :
    JointMeasuredMarkedState representative.carrier :=
  (⟨⟨Set.univ, isCompact_univ⟩, Set.univ_nonempty⟩, representative.marks, representative.masses)

def OriginalJointCompactCoupling.cost {first last : OriginalJointCompactRepresentative}
    (coupling : OriginalJointCompactCoupling first last) : ℝ :=
  jointMeasuredMarkedStateCost
    (jointMeasuredMarkedStateMap coupling.firstPlacement coupling.firstIsometry.continuous
      (originalJointRepresentativeState first))
    (jointMeasuredMarkedStateMap coupling.lastPlacement coupling.lastIsometry.continuous
      (originalJointRepresentativeState last)) +
  dist (skorokhodCadlagContinuousCarrierMapCompletion20261011 coupling.firstPlacement
      coupling.firstIsometry.continuous first.path)
    (skorokhodCadlagContinuousCarrierMapCompletion20261011 coupling.lastPlacement
      coupling.lastIsometry.continuous last.path)

def OriginalJointCompactCoupling.reverse {first last : OriginalJointCompactRepresentative}
    (coupling : OriginalJointCompactCoupling first last) : OriginalJointCompactCoupling last first where
  ambient := coupling.ambient
  firstPlacement := coupling.lastPlacement
  firstIsometry := coupling.lastIsometry
  lastPlacement := coupling.firstPlacement
  lastIsometry := coupling.firstIsometry

def OriginalJointCompactCoupling.reflexive (representative : OriginalJointCompactRepresentative) :
    OriginalJointCompactCoupling representative representative where
  ambient := representative.carrier
  firstPlacement := id
  firstIsometry := isometry_id
  lastPlacement := id
  lastIsometry := isometry_id

theorem OriginalJointCompactCoupling.cost_nonnegative
    {first last : OriginalJointCompactRepresentative}
    (coupling : OriginalJointCompactCoupling first last) : 0 ≤ coupling.cost := by
  unfold cost jointMeasuredMarkedStateCost
  exact add_nonneg (add_nonneg (add_nonneg dist_nonneg
    (Finset.sum_nonneg fun _ _ => dist_nonneg))
    (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)) dist_nonneg

end
end IGSIII34.Diffusion
