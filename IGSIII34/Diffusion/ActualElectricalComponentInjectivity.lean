import IGSIII34.Diffusion.ActualStationaryComponentInverseBound
import IGSIII34.ResistanceLimit.ElectricalComponentBlockBirth
import IGSIII34.Topology.CompletionClosedImage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry MeasureTheory

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // ComponentElectricalTypical rule p positive belowOne fixedPoint growth value marks})
  (coarse : ℕ) (word : Fin (coarse + 1) → Fin rule.edges × Bool)
  (live : retainedComponentState rule marks.val (List.ofFn word) ≠ .inactive)
  (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
    (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
      growth * electricalField rule p positive belowOne fixedPoint value address marks.val)

def actualElectricalComponentInverseConstant : ℝ :=
  stationaryBlockComponentInverseConstant rule marks.val
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val)
    growth coarse (generationWordEdge rule coarse (fun index => (word index).1))

include growthPositive in
theorem actualElectricalComponentInverseConstant_nonnegative :
    0 ≤ actualElectricalComponentInverseConstant rule p positive belowOne fixedPoint growth value marks coarse word := by
  unfold actualElectricalComponentInverseConstant stationaryBlockComponentInverseConstant
  exact mul_nonneg (pow_pos growthPositive _).le (add_nonneg zero_le_one
    (mul_nonneg (stationaryBlockBoundaryEnergyConstant_nonnegative rule marks.val _ growth growthPositive marks.property.1 coarse _)
      (mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (marks.property.1 _)).le))

include live stationary in
/-- The actual coarse factor controls inverse distance for every original
born pair, independently of its later refinement depth. -/
theorem actualElectricalComponentFiniteInclusion_inverse_bound (fine : ℕ)
    (first last : RetainedComponentVertex (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine)
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected) :
    pairResistance (network (rule.generation fine).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine))
      (actualElectricalComponentResistance rule p positive belowOne fixedPoint growth value marks (List.ofFn word) fine) first.val last.val ≤
      actualElectricalComponentInverseConstant rule p positive belowOne fixedPoint growth value marks coarse word *
      dist (actualElectricalComponentFiniteInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live fine first)
        (actualElectricalComponentFiniteInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live fine last) := by
  rw [actualElectricalComponentFiniteInclusion_block_birth, actualElectricalComponentFiniteInclusion_block_birth,
    actualStationaryElectricalVertex_distance]
  simp only [retainedBlockComponentEmbedding, Function.Embedding.coeFn_mk, actualElectricalComponentBlockVertex_val]
  have configurationIdentity := actualElectricalComponentConfiguration_chosen rule p positive belowOne fixedPoint growth value marks coarse word live fine
  have comparison := stationary_actual_block_component_inverse_bound rule marks.val
    (fun address => electricalField rule p positive belowOne fixedPoint value address marks.val) growth growthPositive
    marks.property.1 marks.property.2.1 stationary coarse fine
    (generationWordEdge rule coarse (fun index => (word index).1))
    (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected first.val last.val
    (by rw [← configurationIdentity]; exact first.property)
    (by rw [← configurationIdentity]; exact last.property)
  rw [← configurationIdentity] at comparison
  have addressIdentity : generationEdgeAddress rule coarse (generationWordEdge rule coarse (fun index => (word index).1)) =
      componentEdgeAddress (List.ofFn word) := by
    simp only [generationWordEdge_address, componentEdgeAddress, List.map_ofFn, Function.comp_def]
  rw [addressIdentity] at comparison
  exact comparison

include live stationary in
theorem actualElectricalComponentSkeletonInclusion_inverse_bound
    (first last : ActualElectricalComponentSkeleton rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word)) :
    dist first last ≤ actualElectricalComponentInverseConstant rule p positive belowOne fixedPoint growth value marks coarse word *
      dist (actualElectricalComponentSkeletonInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live first)
        (actualElectricalComponentSkeletonInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live last) := by
  refine DirectLimit.induction₂ (Universality.Geometry.IsometricSequence.transition
    (fun depth => RetainedComponentVertex (rule.generation depth).network
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word) depth)
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected)
    (retainedComponentOldEmbedding rule
      (actualElectricalComponentConfiguration rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
      (actualElectricalComponentCoherent rule p positive belowOne fixedPoint growth value marks (List.ofFn word))
      (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected)) (fun fine first last => ?_) first last
  change dist (rootedElectricalSkeletonVertex rule _ _ _ _ _ _ fine first)
      (rootedElectricalSkeletonVertex rule _ _ _ _ _ _ fine last) ≤ _
  rw [rootedElectricalSkeletonVertex_distance]
  exact actualElectricalComponentFiniteInclusion_inverse_bound rule p positive belowOne fixedPoint growth value growthPositive marks coarse word live stationary fine first last

include live stationary in
/-- The original completed map is uniformly invertible on its image and
therefore a genuine inclusion of the intrinsic physical component. -/
theorem actualElectricalComponentCompletionInclusion_antilipschitz :
    AntilipschitzWith (Real.toNNReal (actualElectricalComponentInverseConstant rule p positive belowOne fixedPoint growth value marks coarse word))
      (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live) := by
  apply IGSIII34.Topology.completion_antilipschitz_of_skeleton_bound
    (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live)
    (actualElectricalComponentCompletionInclusion_lipschitz rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live).continuous
  intro first last
  rw [Real.coe_toNNReal _ (actualElectricalComponentInverseConstant_nonnegative rule p positive belowOne fixedPoint growth value growthPositive marks coarse word)]
  simpa only [actualElectricalComponentCompletionInclusion, UniformSpace.Completion.extension_coe
    (actualElectricalComponentSkeletonInclusion_lipschitz rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live).uniformContinuous] using
    actualElectricalComponentSkeletonInclusion_inverse_bound rule p positive belowOne fixedPoint growth value growthPositive marks coarse word live stationary first last

include live stationary in
theorem actualElectricalComponentCompletionInclusion_injective :
    Function.Injective (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live) :=
  (actualElectricalComponentCompletionInclusion_antilipschitz rule p positive belowOne fixedPoint growth value growthPositive marks coarse word live stationary).injective

include live stationary in
theorem actualElectricalComponentCompletionInclusion_closed_range :
    IsClosed (Set.range (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live)) :=
  (actualElectricalComponentCompletionInclusion_antilipschitz rule p positive belowOne fixedPoint growth value growthPositive marks coarse word live stationary).isClosed_range
    (actualElectricalComponentCompletionInclusion_lipschitz rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live).uniformContinuous

include live stationary in
theorem actualElectricalComponentCompletionInclusion_isClosedEmbedding :
    _root_.Topology.IsClosedEmbedding
      (actualElectricalComponentCompletionInclusion rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live) :=
  (actualElectricalComponentCompletionInclusion_antilipschitz rule p positive belowOne fixedPoint growth value growthPositive marks coarse word live stationary).isClosedEmbedding
    (actualElectricalComponentCompletionInclusion_lipschitz rule p positive belowOne fixedPoint growth value growthPositive marks (List.ofFn word) live).uniformContinuous

end
end IGSIII34.Diffusion
