import IGSIII34.Diffusion.ElectricalHalfOwnershipCompletion
import IGSIII34.Diffusion.VanishingComparison

set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.ResistanceLimit IGSIII34.Percolation
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory Filter
open scoped BigOperators _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (chemicalScale : ℝ) (chemicalScalePositive : 0 < chemicalScale)

local instance electricalDegreeCarrierMeasurableCompletion : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance electricalDegreeCarrierBorelCompletion : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩

def electricalDegreeWordAnchorCompletion (age : ℕ) (word : Fin (age + 1) → (Fin rule.edges × Bool)) :
    ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks :=
  actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks.val marks.property age word

/-- The true reversible degree measure is placed at the same original
retained birth vertices in the actual electrical completion. -/
def actualElectricalDegreeMeasureCompletion (depth : ℕ) :
    Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) :=
  (actualFiniteClusterDegreeMeasure rule (stationaryConfiguration rule marks.val)
    (fun depth => markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 depth [] true)
    chemicalScale chemicalScalePositive depth).map
    (fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive depth =>
      actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)

instance actualElectricalDegreeMeasure_probability_completion (depth : ℕ) :
    IsProbabilityMeasure (actualElectricalDegreeMeasureCompletion rule p positive belowOne fixedPoint growth value growthPositive
      marks chemicalScale chemicalScalePositive depth) := by
  unfold actualElectricalDegreeMeasureCompletion
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

theorem actualElectrical_degree_projection_bound_completion
    (fieldLimit : ∀ address, Tendsto
      (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address) atTop
      (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (fine age : ℕ) (beyond : start ≤ age + 1) (fallback : Fin (age + 1) → (Fin rule.edges × Bool)) :
    levyProkhorovEDist
      (actualElectricalDegreeMeasureCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
        chemicalScale chemicalScalePositive (fine + (age + 1)))
      ((edgeComponentWordLaw rule marks.val marks.property.2.1 fine (age + 1)).map
        (electricalDegreeWordAnchorCompletion rule p positive belowOne fixedPoint growth value growthPositive marks age)) ≤
      ENNReal.ofReal (coefficient * eta ^ (age + 1)) := by
  classical
  letI := clusterEdge_nonempty (rule.generation (fine + (age + 1))).network
    (stationaryConfiguration rule marks.val (fine + (age + 1)))
    (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 _ [] true)
  let inclusion := fun vertex : ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (fine + (age + 1)) =>
    actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (fine + (age + 1)) vertex
  let owner := actualComponentEdgeOwnership rule marks.val marks.property.2.1 fine (age + 1) fallback
  let anchor : (Fin (age + 1) → (Fin rule.edges × Bool)) →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks :=
    electricalDegreeWordAnchorCompletion rule p positive belowOne fixedPoint growth value growthPositive marks age
  have close edge side : dist
      (inclusion (halfEndpoint (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val)
        chemicalScale chemicalScalePositive (fine + (age + 1)))
        (clusterRetainedEndpoint (rule.generation (fine + (age + 1))).network _) (edge, side)))
      (anchor (owner edge)) ≤ coefficient * eta ^ (age + 1) :=
    actualElectrical_halfowner_mesh_completion rule p positive belowOne fixedPoint growth value growthPositive marks
      fieldLimit eta coefficient start radiusBound chemicalScale chemicalScalePositive fine age beyond fallback edge side
  have estimate := degree_projection_bound
    (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive (fine + (age + 1)))
    (clusterRetainedEndpoint (rule.generation (fine + (age + 1))).network _) inclusion owner anchor (coefficient * eta ^ (age + 1))
    (mul_nonneg coefficientNonnegative (pow_nonneg etaNonnegative _))
    (fun edge => ⟨by simpa only [halfEndpoint, if_true] using close edge true,
      by simpa only [halfEndpoint, Bool.false_eq_true, if_false] using close edge false⟩)
  have law := congrArg (fun measure => measure.map anchor)
    (actual_half_owner_law rule marks.val marks.property.2.1 fine (age + 1) fallback)
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at law
  simp only [Function.comp_def] at law
  change levyProkhorovEDist
    ((degreeMeasure (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive
      (fine + (age + 1))) (clusterRetainedEndpoint (rule.generation (fine + (age + 1))).network _)).map inclusion)
    ((edgeComponentWordLaw rule marks.val marks.property.2.1 fine (age + 1)).map anchor) ≤ _
  exact Eq.mp (congrArg (fun measure => levyProkhorovEDist
    ((degreeMeasure (Vertex := ActualFiniteCluster rule (stationaryConfiguration rule marks.val) chemicalScale chemicalScalePositive
      (fine + (age + 1))) (clusterRetainedEndpoint (rule.generation (fine + (age + 1))).network _)).map inclusion) measure ≤
      ENNReal.ofReal (coefficient * eta ^ (age + 1))) law) estimate

end
end IGSIII34.Diffusion
