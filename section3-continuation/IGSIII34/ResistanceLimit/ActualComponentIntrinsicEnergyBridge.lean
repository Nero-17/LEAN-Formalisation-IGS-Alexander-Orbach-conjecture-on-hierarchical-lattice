import IGSIII34.Forms.ComponentBlockVertex
import IGSIII34.Forms.ActualComponentEnergyBound
import IGSIII34.Forms.RetainedWordScaling
import IGSIII34.Forms.CompletionExtension
import IGSIII34.Diffusion.ActualElectricalComponentRestriction
import IGSIII34.ResistanceLimit.ElectricalComponentBlockBirth
import IGSIII34.ResistanceLimit.HarmonicTower

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.Forms IGSIII34.Diffusion
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (energyTypical : StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks.val)

def actualComponentEnergyMarks :
    {marks // StationaryEnergyTypical rule p positive belowOne fixedPoint growth value marks} :=
  ⟨marks.val, energyTypical⟩

variable (potential : energyDomain
  (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical))
  (actualEnergyConductance rule p positive belowOne fixedPoint growth value
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical))
  (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical)))

def actualComponentGlobalEnergyExtension :
    C(ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive
      (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks), ℝ) :=
  completionExtension
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical))
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical))
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical)) potential

theorem actualComponentGlobalEnergyExtension_born (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (stationaryConfiguration rule marks.val depth)) :
    actualComponentGlobalEnergyExtension rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential
      (actualStationaryElectricalVertex rule p positive belowOne fixedPoint growth value growthPositive
        (componentTypicalRootElectricalMarks rule p positive belowOne fixedPoint growth value marks) depth vertex) =
    actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) potential.val depth vertex.val := by
  unfold actualComponentGlobalEnergyExtension actualStationaryElectricalVertex actualComponentPotentialStage
  rw [electricalSkeletonPoint_retained]
  exact completionExtension_coe _ _ _
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical)) potential _

variable (coarse : ℕ) (word : Fin (coarse + 1) → Fin rule.edges × Bool)
  (live : retainedComponentState rule marks.val (List.ofFn word) ≠ .inactive)

def actualComponentIntrinsicRestriction :
    ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) → ℝ :=
  fun point => actualComponentGlobalEnergyExtension rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential
    (actualElectricalComponentSkeletonInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live point)

theorem actualComponentIntrinsicRestriction_finite_trace (fine : ℕ) :
    retainedWordTraceEnergy rule marks.val marks.property.2.1 fine (coarse + 1)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val (fine + (coarse + 1)))
      (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive
        (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) potential.val (fine + (coarse + 1))) word =
    growth ^ (coarse + 1) * rootedElectricalIntrinsicTraceEnergy rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
      (actualElectricalComponentResistance_positive rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word))
      (actualElectricalComponentResistance_compatible rule p positive belowOne fixedPoint growth value marks (List.ofFn word)) fine
      (actualComponentIntrinsicRestriction rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential coarse word live) := by
  unfold stationaryResistance
  erw [retainedWordTraceEnergy_stationary_scaling]
  rw [actualElectricalComponentIntrinsicTraceEnergy_eq_selected rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live]
  congr 1
  rw [selectedComponentTraceEnergy, if_neg live, selectedComponentTraceEnergy, if_neg live]
  apply sourceComponentEnergy_congr_retained
  intro vertex retained
  rw [sideNetwork_graph, graph_eq_openGraph, sideNetwork_network_source] at retained
  let localVertex : RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine)
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected := ⟨vertex, retained⟩
  change actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) potential.val (fine + (coarse + 1))
      ((generationComponentWordEmbedding rule fine (coarse + 1) (fun index => (word index).1)).vertex vertex) = _
  rw [rootedElectricalSkeletonPoint_retained (vertex := localVertex)]
  unfold actualComponentIntrinsicRestriction
  rw [actualElectricalComponentSkeletonInclusion_mk,
    actualElectricalComponentFiniteInclusion_block_birth]
  rw [actualComponentGlobalEnergyExtension_born]
  have embedding := generationComponentWordEmbedding_block_vertex rule coarse fine (fun index => (word index).1)
    (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected
    (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine) vertex retained
  have castValue := finitePotential_apply_index_cast (fun depth => (rule.generation depth).vertices)
    (actualComponentPotentialStage rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) potential.val)
    (by omega : coarse + fine + 1 = fine + (coarse + 1))
    (congrArg (fun depth => (rule.generation depth).vertices) (by omega : fine + (coarse + 1) = coarse + fine + 1))
    ((generationComponentWordEmbedding rule fine (coarse + 1) (fun index => (word index).1)).vertex vertex)
  rw [embedding] at castValue
  exact castValue.symm

/-- The actual global finite-energy domain restricts to the genuine local
intrinsic finite-energy domain. Boundedness comes from the finite partition. -/
theorem actualComponentIntrinsicRestriction_finite :
    actualElectricalComponentIntrinsicFiniteEnergy rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word)
      (actualComponentIntrinsicRestriction rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential coarse word live) := by
  obtain ⟨upper, bound⟩ := actualRetainedComponent_trace_bddAbove rule p positive belowOne fixedPoint growth value growthPositive
    (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) potential.val potential.property (coarse + 1) word
  refine ⟨upper / growth ^ (coarse + 1), ?_⟩
  rintro energy ⟨fine, rfl⟩
  apply (le_div_iff₀ (pow_pos growthPositive (coarse + 1))).mpr
  rw [mul_comm, ← actualComponentIntrinsicRestriction_finite_trace]
  exact bound (Set.mem_range_self fine)

/-- The decomposition piece and the intrinsic completed component energy
are exactly the same energy under the paper's electrical normalization. -/
theorem actualRetainedComponentEnergy_eq_intrinsic_restriction :
    actualRetainedComponentEnergy rule p positive belowOne fixedPoint growth value growthPositive
      (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) potential.val (coarse + 1) word =
    growth ^ (coarse + 1) * actualElectricalComponentIntrinsicEnergy rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word)
      (actualComponentIntrinsicRestriction rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential coarse word live) := by
  unfold actualRetainedComponentEnergy actualElectricalComponentIntrinsicEnergy rootedElectricalIntrinsicEnergy
  rw [Real.mul_iSup_of_nonneg (pow_pos growthPositive (coarse + 1)).le]
  congr 1
  funext fine
  exact actualComponentIntrinsicRestriction_finite_trace rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential coarse word live fine

/-- The local extension is the restriction of the SAME global extension
at every completion point, rather than merely at finite vertices. -/
theorem actualComponentIntrinsicRestriction_completed
    (point : ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word)) :
    actualComponentGlobalEnergyExtension rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential
      (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live point) =
    actualElectricalComponentIntrinsicExtension rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word)
      (actualComponentIntrinsicRestriction rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential coarse word live) point := by
  apply actualElectricalComponent_completed_restriction_of_born rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live
    (actualComponentIntrinsicRestriction rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential coarse word live)
    (actualComponentIntrinsicRestriction_finite rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential coarse word live)
    (actualComponentGlobalEnergyExtension rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential)
  intro fine vertex
  unfold actualComponentIntrinsicRestriction
  rw [actualElectricalComponentSkeletonInclusion_mk]

/-- The intrinsic resistance inequality now binds to the precise piece in
the global completed-form decomposition. -/
theorem actual_completed_component_resistance_bound
    (first last : ActualElectricalComponentSpace rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word)) :
    (actualComponentGlobalEnergyExtension rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential
        (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live first) -
      actualComponentGlobalEnergyExtension rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential
        (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live last)) ^ 2 ≤
      dist first last * (actualRetainedComponentEnergy rule p positive belowOne fixedPoint growth value growthPositive
        (actualComponentEnergyMarks rule p positive belowOne fixedPoint growth value marks energyTypical) potential.val (coarse + 1) word / growth ^ (coarse + 1)) := by
  rw [actualComponentIntrinsicRestriction_completed, actualComponentIntrinsicRestriction_completed,
    actualRetainedComponentEnergy_eq_intrinsic_restriction, mul_div_cancel_left₀ _ (pow_pos growthPositive (coarse + 1)).ne']
  exact actualElectricalComponent_completed_intrinsic_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word)
    (actualComponentIntrinsicRestriction rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential coarse word live)
    (actualComponentIntrinsicRestriction_finite rule p positive belowOne fixedPoint growth value growthPositive marks energyTypical potential coarse word live) first last

end
end IGSIII34.ResistanceLimit
