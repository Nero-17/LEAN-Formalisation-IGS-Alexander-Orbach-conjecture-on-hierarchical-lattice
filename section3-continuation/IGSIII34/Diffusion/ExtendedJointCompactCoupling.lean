import IGSIII34.Diffusion.ExtendedJointCompactRepresentative
import IGSIII34.Diffusion.OriginalJointCompactDistanceBasic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory TopologicalSpace Metric
open scoped ENNReal BigOperators

/-- A coupling consists of true isometric placements into one compact
ambient. No distance-profile homeomorphism is substituted for an isometry. -/
structure ExtendedJointCompactCoupling
    (first last : ExtendedJointCompactRepresentative) where
  ambient : NonemptyCompacts OriginalJointUniversalSpace
  firstPlacement : first.ambient → ambient
  firstIsometry : Isometry firstPlacement
  lastPlacement : last.ambient → ambient
  lastIsometry : Isometry lastPlacement

def ExtendedJointCompactCoupling.cost {first last : ExtendedJointCompactRepresentative}
    (coupling : ExtendedJointCompactCoupling first last) : ℝ :=
  jointMeasuredMarkedStateCost
    (jointMeasuredMarkedStateMap coupling.firstPlacement coupling.firstIsometry.continuous
      first.state)
    (jointMeasuredMarkedStateMap coupling.lastPlacement coupling.lastIsometry.continuous
      last.state) +
  dist (skorokhodCadlagContinuousCarrierMapCompletion20261011 coupling.firstPlacement
      coupling.firstIsometry.continuous first.path)
    (skorokhodCadlagContinuousCarrierMapCompletion20261011 coupling.lastPlacement
      coupling.lastIsometry.continuous last.path)

def ExtendedJointCompactCoupling.reverse {first last : ExtendedJointCompactRepresentative}
    (coupling : ExtendedJointCompactCoupling first last) : ExtendedJointCompactCoupling last first where
  ambient := coupling.ambient
  firstPlacement := coupling.lastPlacement
  firstIsometry := coupling.lastIsometry
  lastPlacement := coupling.firstPlacement
  lastIsometry := coupling.firstIsometry

def ExtendedJointCompactCoupling.reflexive (representative : ExtendedJointCompactRepresentative) :
    ExtendedJointCompactCoupling representative representative where
  ambient := representative.ambient
  firstPlacement := id
  firstIsometry := isometry_id
  lastPlacement := id
  lastIsometry := isometry_id

theorem ExtendedJointCompactCoupling.cost_nonnegative
    {first last : ExtendedJointCompactRepresentative}
    (coupling : ExtendedJointCompactCoupling first last) : 0 ≤ coupling.cost := by
  unfold cost jointMeasuredMarkedStateCost
  exact add_nonneg (add_nonneg (add_nonneg dist_nonneg
    (Finset.sum_nonneg fun _ _ => dist_nonneg))
    (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)) dist_nonneg

theorem ExtendedJointCompactCoupling.exists
    (first last : ExtendedJointCompactRepresentative) :
    Nonempty (ExtendedJointCompactCoupling first last) := by
  letI : MetricSpace (first.ambient ⊕ last.ambient) := metricSpaceSum
  let embedding := (kuratowskiEmbedding.isometry
    (first.ambient ⊕ last.ambient)).isometryEquivOnRange
  exact ⟨{
    ambient := NonemptyCompacts.kuratowskiEmbedding (first.ambient ⊕ last.ambient)
    firstPlacement := embedding ∘ Sum.inl
    firstIsometry := embedding.isometry.comp isometry_inl
    lastPlacement := embedding ∘ Sum.inr
    lastIsometry := embedding.isometry.comp isometry_inr }⟩

theorem ExtendedJointCompactCoupling.cost_reflexive
    (representative : ExtendedJointCompactRepresentative) :
    (ExtendedJointCompactCoupling.reflexive representative).cost = 0 := by
  simp [ExtendedJointCompactCoupling.cost, ExtendedJointCompactCoupling.reflexive,
    jointMeasuredMarkedStateCost, levyProkhorovDist_self]

theorem ExtendedJointCompactCoupling.cost_reverse
    {first last : ExtendedJointCompactRepresentative}
    (coupling : ExtendedJointCompactCoupling first last) : coupling.reverse.cost = coupling.cost := by
  simp only [ExtendedJointCompactCoupling.cost, ExtendedJointCompactCoupling.reverse,
    jointMeasuredMarkedStateCost, dist_comm, levyProkhorovDist_comm]


/-- Original and extended couplings have exactly the same placements and
cost on original representatives. -/
def OriginalJointCompactCoupling.toExtended
    {first last : OriginalJointCompactRepresentative}
    (coupling : OriginalJointCompactCoupling first last) :
    ExtendedJointCompactCoupling (.ofOriginal first) (.ofOriginal last) where
  ambient := coupling.ambient
  firstPlacement := coupling.firstPlacement
  firstIsometry := coupling.firstIsometry
  lastPlacement := coupling.lastPlacement
  lastIsometry := coupling.lastIsometry

def ExtendedJointCompactCoupling.toOriginal
    {first last : OriginalJointCompactRepresentative}
    (coupling : ExtendedJointCompactCoupling (.ofOriginal first) (.ofOriginal last)) :
    OriginalJointCompactCoupling first last where
  ambient := coupling.ambient
  firstPlacement := coupling.firstPlacement
  firstIsometry := coupling.firstIsometry
  lastPlacement := coupling.lastPlacement
  lastIsometry := coupling.lastIsometry

@[simp] theorem OriginalJointCompactCoupling.toExtended_cost
    {first last : OriginalJointCompactRepresentative}
    (coupling : OriginalJointCompactCoupling first last) : coupling.toExtended.cost = coupling.cost := rfl

@[simp] theorem ExtendedJointCompactCoupling.toOriginal_cost
    {first last : OriginalJointCompactRepresentative}
    (coupling : ExtendedJointCompactCoupling (.ofOriginal first) (.ofOriginal last)) :
    coupling.toOriginal.cost = coupling.cost := rfl

end
end IGSIII34.Diffusion
