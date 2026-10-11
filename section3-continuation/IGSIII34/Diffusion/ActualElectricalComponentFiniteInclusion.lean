import IGSIII34.Diffusion.ActualElectricalComponentCompletion
import IGSIII.Geometry.AddressMetricPersistence
import IGSIII34.ResistanceLimit.Rayleigh
import IGSIII34.ResistanceLimit.PairContinuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2600000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry

theorem generationEdgeAddress_addressEmbedding (rule : Rule) (address : List (Fin rule.edges))
    (fine : ℕ) (edge : Fin (rule.generation fine).edges) :
    generationEdgeAddress rule (fine + address.length) ((generationAddressEmbedding rule address fine).edge edge) =
      address ++ generationEdgeAddress rule fine edge := by
  induction address with
  | nil => rfl
  | cons choice tail previous =>
    change generationEdgeAddress rule ((fine + tail.length) + 1)
      ((rule.generationTopDecomposition (fine + tail.length)).edge.symm
        (finProdFinEquiv (choice, (generationAddressEmbedding rule tail fine).edge edge))) = _
    rw [generationEdgeAddress_top, previous]
    simp only [List.cons_append]

theorem stationary_generation_address_resistance_scaling (rule : Rule) (field : List (Fin rule.edges) → ℝ)
    (growth : ℝ) (address : List (Fin rule.edges)) (fine : ℕ) (edge : Fin (rule.generation fine).edges) :
    stationaryGenerationResistance rule field growth (fine + address.length) []
      ((generationAddressEmbedding rule address fine).edge edge) =
      growth⁻¹ ^ address.length * stationaryGenerationResistance rule field growth fine address edge := by
  unfold stationaryGenerationResistance
  rw [generationEdgeAddress_addressEmbedding]
  simp only [List.nil_append]
  rw [show fine + address.length + 1 = address.length + (fine + 1) by omega, pow_add]
  ring

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : MeasureTheory.Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (word : List (Fin rule.edges × Bool))
  (live : retainedComponentState rule marks.val word ≠ .inactive)

def componentTypicalRootElectricalMarks :
    {marks // StationaryElectricalTypical rule p positive belowOne fixedPoint growth value marks} :=
  ⟨marks.val, marks.property.1, marks.property.2.1,
    fun depth first last reachable => marks.property.2.2 depth [] true first last reachable⟩

/-- Every vertex of the actual live selected component is placed into the
actual full root cluster by its original address embedding. -/
def actualElectricalComponentRetainedEmbedding (fine : ℕ) :
    RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word fine)
      (retainedComponentState rule marks.val word).sourceSelected ↪
    RetainedSkeletonVertex (rule.generation (fine + (componentEdgeAddress word).length)).network
      (stationaryConfiguration rule marks.val (fine + (componentEdgeAddress word).length)) where
  toFun vertex := ⟨(generationAddressEmbedding rule (componentEdgeAddress word) fine).vertex vertex.val, by
    have selected := (marked_component_selected_iff rule marks.val marks.property.2.1 fine word live vertex.val).mpr vertex.property
    have inherited := generationAddressEmbedding_selected_component rule marks.val marks.property.2.1 fine [] .connected word live vertex.val (by
      simpa only [retainedComponentState, List.nil_append] using selected)
    exact (single_oriented_component_selected_iff (rule.generation (fine + (componentEdgeAddress word).length)).network
      (stationaryConfiguration rule marks.val (fine + (componentEdgeAddress word).length)) .connected
      (by decide) (by decide) (markedGenerationConfiguration_crosses rule marks.val marks.property.2.1 _ [] true) _).mp inherited⟩
  inj' := by
    intro first last equality
    exact Subtype.ext ((generationAddressEmbedding rule (componentEdgeAddress word) fine).vertex.injective (congrArg Subtype.val equality))

def actualElectricalComponentFiniteInclusion (fine : ℕ)
    (vertex : RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word fine)
      (retainedComponentState rule marks.val word).sourceSelected) :
    ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) :=
  actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
    (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks)
    (fine + (componentEdgeAddress word).length)
    (actualElectricalComponentRetainedEmbedding rule p positive belowOne fixedPoint growth value marks word live fine vertex)

/-- Rayleigh's inequality with the exact original address scaling. -/
theorem actualElectricalComponentFiniteInclusion_resistance_le (fine : ℕ)
    (first last : RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word fine)
      (retainedComponentState rule marks.val word).sourceSelected) :
    dist (actualElectricalComponentFiniteInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live fine first)
      (actualElectricalComponentFiniteInclusion rule p positive belowOne fixedPoint growth value growthPositive marks word live fine last) ≤
    growth⁻¹ ^ (componentEdgeAddress word).length *
      pairResistance (network (rule.generation fine).network (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word fine))
        (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word fine) first.val last.val := by
  let embedding := generationAddressEmbedding rule (componentEdgeAddress word) fine
  have restriction := generationAddressEmbedding_restrict_marked_component rule marks.val fine [] .connected word live
  simp only [List.nil_append] at restriction
  change embedding.restrict (stationaryConfiguration rule marks.val (fine + (componentEdgeAddress word).length)) =
    actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word fine at restriction
  let edges : {edge : Fin (rule.generation fine).edges // actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word fine edge = true} ↪
      {edge : Fin (rule.generation (fine + (componentEdgeAddress word).length)).edges // stationaryConfiguration rule marks.val (fine + (componentEdgeAddress word).length) edge = true} :=
    ⟨fun edge => ⟨embedding.edge edge.val, by
      change embedding.restrict (stationaryConfiguration rule marks.val (fine + (componentEdgeAddress word).length)) edge.val = true
      rw [restriction]
      exact edge.property⟩, by
      intro first last equality
      exact Subtype.ext (embedding.edge.injective (congrArg Subtype.val equality))⟩
  have scalarPositive := pow_pos (inv_pos.mpr growthPositive) (componentEdgeAddress word).length
  have bound := embedded_pairResistance_le
    (network (rule.generation fine).network (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks word fine))
    (network (rule.generation (fine + (componentEdgeAddress word).length)).network (stationaryConfiguration rule marks.val (fine + (componentEdgeAddress word).length)))
    embedding.vertex edges (fun edge => embedding.endpoint edge.val)
    (fun edge => growth⁻¹ ^ (componentEdgeAddress word).length * actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks word fine edge)
    (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val (fine + (componentEdgeAddress word).length))
    (fun edge => mul_pos scalarPositive (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word fine edge))
    (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) (fine + (componentEdgeAddress word).length))
    (fun edge => stationary_generation_address_resistance_scaling rule
      (fun descendant => electricalField rule p positive belowOne fixedPoint value descendant marks.val)
      growth (componentEdgeAddress word) fine edge.val)
    first.val last.val (by rw [graph_eq_openGraph]; exact first.property.symm.trans last.property)
  rw [pairResistance_scale _ _
    (fun edge => (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks word fine edge).le)
    _ scalarPositive.le] at bound
  simpa only [actualElectricalComponentFiniteInclusion, actualStationaryElectricalVertex_distance,
    actualElectricalComponentRetainedEmbedding, Function.Embedding.coeFn_mk, componentTypicalRootElectricalMarks, embedding] using bound

end
end IGSIII34.Diffusion
