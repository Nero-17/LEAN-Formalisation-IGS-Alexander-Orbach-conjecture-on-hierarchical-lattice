import IGSIII34.Diffusion.ElectricalDegreeProjectionCompletion20261011
import IGSIII.Geometry.ActualComponentOwnershipMetric
import IGSIII.Geometry.ExceptionalTransport

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
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

local instance electricalCountingCarrierMeasurableCompletion20261011 : MeasurableSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := borel _
local instance electricalCountingCarrierBorelCompletion20261011 : BorelSpace
    (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) := ⟨rfl⟩

/-- Uniform counting probability is placed at the same actual born vertices. -/
def actualElectricalCountingMeasureCompletion20261011 (depth : ℕ) :
    Measure (ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive marks) :=
  (actualFiniteClusterMeasure rule ((fun depth => markedGenerationConfiguration rule marks.val depth [] true)) chemicalScale chemicalScalePositive depth).map
    (fun vertex : ActualFiniteCluster rule ((fun depth => markedGenerationConfiguration rule marks.val depth [] true)) chemicalScale chemicalScalePositive depth =>
      actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks depth vertex)

instance actualElectricalCountingMeasure_probability_completion20261011 (depth : ℕ) :
    IsProbabilityMeasure (actualElectricalCountingMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value
      growthPositive marks chemicalScale chemicalScalePositive depth) := by
  unfold actualElectricalCountingMeasureCompletion20261011
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

theorem actualElectrical_vertexowner_mesh_completion20261011
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (fine age : ℕ) (beyond : start ≤ age + 1)
    (fallback : Fin (age + 1) → (Fin rule.edges × Bool))
    (point : ActualFiniteCluster rule ((fun depth => markedGenerationConfiguration rule marks.val depth [] true)) chemicalScale chemicalScalePositive (fine + (age + 1)))
    (nonfrontier : point ∉ actualComponentVertexFrontier rule marks.val marks.property.2.1
      chemicalScale chemicalScalePositive fine (age + 1)) :
    dist (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (fine + (age + 1)) point)
      (electricalDegreeWordAnchorCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks age
        (actualComponentVertexOwnership rule marks.val marks.property.2.1 chemicalScale chemicalScalePositive fine (age + 1) fallback point)) ≤
      coefficient * eta ^ (age + 1) := by
  obtain ⟨child, childIdentity⟩ := actualComponentVertexOwnership_nonfrontier
    rule marks.val marks.property.2.1 chemicalScale chemicalScalePositive fine (age + 1) fallback point nonfrontier
  let word := actualComponentVertexOwnership rule marks.val marks.property.2.1 chemicalScale chemicalScalePositive fine (age + 1) fallback point
  have live : retainedComponentState rule marks.val (List.ofFn word) ≠ .inactive :=
    selectedComponentInterior_live rule marks.val fine _ _ child
  have reachable := (marked_component_selected_iff rule marks.val marks.property.2.1 fine (List.ofFn word) live child.val.val).mp child.property
  have rawIdentity : point.val =
      (generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex child.val.val := by
    have equality := congrArg (fun vertex : ActualFiniteCluster rule
      ((fun depth => markedGenerationConfiguration rule marks.val depth [] true)) chemicalScale chemicalScalePositive (fine + (age + 1)) => vertex.val) childIdentity
    change (selectedComponentWordEmbedding rule marks.val marks.property.2.1 fine (age + 1) [] .connected ⟨word, child⟩).val.val = point.val at equality
    rw [selectedComponentWordEmbedding_vertex] at equality
    exact equality.symm
  have retained : ((rule.generation (fine + (age + 1))).network.openGraph
      ((fun depth => markedGenerationConfiguration rule marks.val depth [] true) (fine + (age + 1)))).Reachable
      (rule.generation (fine + (age + 1))).network.source
      ((generationComponentWordEmbedding rule fine (age + 1) (fun index => (word index).1)).vertex child.val.val) :=
    rawIdentity ▸ point.property
  have estimate := actualElectrical_word_mesh_completion20261011 rule p positive belowOne fixedPoint growth value growthPositive
    marks fieldLimit eta coefficient start radiusBound fine age beyond word live child.val.val reachable retained
  have pointIdentity : (⟨_, retained⟩ : ActualFiniteCluster rule ((fun depth => markedGenerationConfiguration rule marks.val depth [] true))
      chemicalScale chemicalScalePositive (fine + (age + 1))) = point := Subtype.ext rawIdentity.symm
  rw [pointIdentity, dist_comm] at estimate
  exact estimate

theorem actualElectrical_counting_projection_bound_completion20261011
    (fieldLimit : ∀ address, Tendsto (fun depth => growth⁻¹ ^ depth * electricalIteration rule marks.val depth address)
      atTop (𝓝 (electricalField rule p positive belowOne fixedPoint value address marks.val)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBound : ∀ address opened depth, start ≤ address.length →
      markedElectricalRadius rule marks.val depth address opened / growth ^ (depth + 1 + address.length) ≤ coefficient * eta ^ address.length)
    (fine age : ℕ) (beyond : start ≤ age + 1) (fallback : Fin (age + 1) → (Fin rule.edges × Bool)) :
    levyProkhorovEDist
      (actualElectricalCountingMeasureCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks
        chemicalScale chemicalScalePositive (fine + (age + 1)))
      ((fullComponentEmpiricalWordLaw rule marks.val marks.property.2.1 fine (age + 1) fallback).map
        (electricalDegreeWordAnchorCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks age)) ≤
      ENNReal.ofReal (coefficient * eta ^ (age + 1)) +
        actualFiniteClusterMeasure rule ((fun depth => markedGenerationConfiguration rule marks.val depth [] true)) chemicalScale chemicalScalePositive (fine + (age + 1))
          (actualComponentVertexFrontier rule marks.val marks.property.2.1 chemicalScale chemicalScalePositive fine (age + 1)) := by
  let inclusion := fun vertex : ActualFiniteCluster rule ((fun depth => markedGenerationConfiguration rule marks.val depth [] true)) chemicalScale chemicalScalePositive (fine + (age + 1)) =>
    actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive marks (fine + (age + 1)) vertex
  let anchor := electricalDegreeWordAnchorCompletion20261011 rule p positive belowOne fixedPoint growth value growthPositive marks age
  let owner := actualComponentVertexOwnership rule marks.val marks.property.2.1 chemicalScale chemicalScalePositive fine (age + 1) fallback
  have estimate := levyProkhorovEDist_map_le_of_exceptional_set
    (actualFiniteClusterMeasure rule ((fun depth => markedGenerationConfiguration rule marks.val depth [] true)) chemicalScale chemicalScalePositive (fine + (age + 1)))
    inclusion (fun point => anchor (owner point)) (measurable_of_finite _) (measurable_of_finite _)
    (actualComponentVertexFrontier rule marks.val marks.property.2.1 chemicalScale chemicalScalePositive fine (age + 1))
    (coefficient * eta ^ (age + 1)) (mul_nonneg coefficientNonnegative (pow_nonneg etaNonnegative _))
    (Eventually.of_forall fun point outside => actualElectrical_vertexowner_mesh_completion20261011
      rule p positive belowOne fixedPoint growth value growthPositive marks chemicalScale chemicalScalePositive
      fieldLimit eta coefficient start radiusBound fine age beyond fallback point outside)
  have law := congrArg (fun measure => measure.map anchor)
    (actualComponentVertexOwnership_law rule marks.val marks.property.2.1 chemicalScale chemicalScalePositive fine (age + 1) fallback)
  rw [Measure.map_map (measurable_of_finite _) (measurable_of_finite _)] at law
  simp only [Function.comp_def] at law
  rw [law] at estimate
  exact estimate

end
end IGSIII34.Diffusion
