import IGSIII34.Spectral.ActualBoundaryHarmonicCompletion
import IGSIII34.Spectral.ActualSocketCutoffGeometryCompletion
import IGSIII34.Spectral.PhysicalSocketMassCompletion
import IGSIII34.ResistanceLimit.ActualHarmonicGlobalRangeCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3500000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms Resistance
open MeasureTheory Filter
open scoped BigOperators _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})
  (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
    (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
      growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
  (boundaryLaw : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
  (retainedPaths : ∀ᵐ path ∂boundaryLaw, ∀ depth,
    Fin.init (path (depth + 1)) = path depth ∧ retainedComponentState rule marks.val (List.ofFn (path depth)) ≠ .inactive)
  (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
    ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
  (convergence : ∀ᵐ path ∂boundaryLaw, Tendsto (fun depth =>
    actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks.val marks.property.1.1
      depth (path (depth + 1))) atTop (𝓝 (realization path)))

include stationary retainedPaths convergence in
theorem actual_physical_root_cutoff_realization_one_completion
    (depth : ℕ) (word : Fin (depth + 1) → (Fin rule.edges × Bool)) :
    ∀ᵐ path ∂boundaryLaw, path (depth + 1) = word →
      actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks depth
        (fun vertex => if vertex ∈ physicalEdgeRootCutoffVerticesCompletion rule depth
          (generationWordEdge rule depth (fun index => (word index).1)) then 1 else 0)
        (realization path) = 1 := by
  have values := actual_harmonic_boundary_realization_prefix_value_completion rule p positive belowOne fixedPoint growth value
    growthPositive marks stationary boundaryLaw retainedPaths realization convergence depth
    (fun vertex => if vertex ∈ physicalEdgeRootCutoffVerticesCompletion rule depth
      (generationWordEdge rule depth (fun index => (word index).1)) then 1 else 0) word
    (fun opened => physical_edge_root_cutoff_projected_flat_completion rule depth
      (stationaryConfiguration rule marks.val depth) _ opened)
  filter_upwards [values] with path equality
  intro member
  exact (equality member).trans (physical_edge_root_cutoff_anchor_value_completion rule marks.val depth word)

include stationary retainedPaths convergence in
theorem actual_parent_binary_cutoff_realization_zero_completion
    (coarse fine : ℕ) (parentEdges : Fin (coarse + 1) → Fin rule.edges)
    (selected : Finset (Fin (rule.generation (coarse + fine + 1)).vertices))
    (internal : ∀ vertex ∈ selected, ∃ inside : (rule.generation fine).network.InteriorVertex,
      (generationBlockCellEmbedding rule coarse fine (generationWordEdge rule coarse parentEdges)).vertex inside.val = vertex) :
    ∀ᵐ path ∂boundaryLaw, path ∉ physicalSocketCylinderCompletion rule (coarse + 1) parentEdges →
      actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
        (coarse + fine + 1) (fun vertex => if vertex ∈ selected then 1 else 0) (realization path) = 0 := by
  classical
  have zeroPrefix (word : Fin (coarse + fine + 2) → (Fin rule.edges × Bool)) :
      ∀ᵐ path ∂boundaryLaw, path (coarse + fine + 2) = word →
        (¬∃ child : Fin (rule.generation fine).edges,
          (generationBlockCellEmbedding rule coarse fine (generationWordEdge rule coarse parentEdges)).edge child =
            generationWordEdge rule (coarse + fine + 1) (fun index => (word index).1)) →
        actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
          (coarse + fine + 1) (fun vertex => if vertex ∈ selected then 1 else 0) (realization path) = 0 := by
    by_cases outside : ¬∃ child : Fin (rule.generation fine).edges,
        (generationBlockCellEmbedding rule coarse fine (generationWordEdge rule coarse parentEdges)).edge child =
          generationWordEdge rule (coarse + fine + 1) (fun index => (word index).1)
    · have zeros := actual_binary_parent_boundary_zero_outside_completion rule coarse fine
        (generationWordEdge rule coarse parentEdges) selected internal
        (generationWordEdge rule (coarse + fine + 1) (fun index => (word index).1)) outside
      have flat : stationaryConfiguration rule marks.val (coarse + fine + 1)
          (generationWordEdge rule (coarse + fine + 1) (fun index => (word index).1)) = true →
          sourceProjection (network (rule.generation (coarse + fine + 1)).network
            (stationaryConfiguration rule marks.val (coarse + fine + 1)))
            (fun vertex => if vertex ∈ selected then 1 else 0)
            ((rule.generation (coarse + fine + 1)).network.endpoint
              (generationWordEdge rule (coarse + fine + 1) (fun index => (word index).1))).1 =
          sourceProjection (network (rule.generation (coarse + fine + 1)).network
            (stationaryConfiguration rule marks.val (coarse + fine + 1)))
            (fun vertex => if vertex ∈ selected then 1 else 0)
            ((rule.generation (coarse + fine + 1)).network.endpoint
              (generationWordEdge rule (coarse + fine + 1) (fun index => (word index).1))).2 := by
        intro _
        unfold sourceProjection
        dsimp only at ⊢
        rw [zeros.1, zeros.2]
        split_ifs <;> rfl
      have values := actual_harmonic_boundary_realization_prefix_value_completion rule p positive belowOne fixedPoint
        growth value growthPositive marks stationary boundaryLaw retainedPaths realization convergence (coarse + fine + 1)
        (fun vertex => if vertex ∈ selected then 1 else 0) word flat
      filter_upwards [values] with path equality
      intro member _
      rw [equality member]
      by_cases selectedSide : (retainedComponentState rule marks.val (List.ofFn word)).sourceSelected = true
      · simpa only [componentWordAnchor, if_pos selectedSide] using zeros.1
      · simpa only [componentWordAnchor, if_neg selectedSide] using zeros.2
    · exact Eventually.of_forall (fun _ _ impossible => (outside impossible).elim)
  filter_upwards [ae_all_iff.mpr zeroPrefix, retainedPaths] with path zeros retained
  intro outside
  have differentWords : (fun index => (path (coarse + 1) index).1) ≠ parentEdges := by
    intro equality
    apply outside
    exact (physical_socket_cylinder_mem_completion rule (coarse + 1) parentEdges path).mpr
      (fun index => congrFun equality index)
  have differentEdges : generationWordEdge rule coarse (fun index => (path (coarse + 1) index).1) ≠
      generationWordEdge rule coarse parentEdges :=
    fun equality => differentWords (generation_word_edge_injective_completion rule coarse equality)
  obtain ⟨suffix, decomposition⟩ := nested_path_block_decomposition_completion path
    (fun depth => (retained depth).1) coarse fine
  have edgeIdentity : generationWordEdge rule (coarse + fine + 1) (fun index => (path (coarse + fine + 2) index).1) =
      (generationBlockCellEmbedding rule coarse fine
        (generationWordEdge rule coarse (fun index => (path (coarse + 1) index).1))).edge
        (generationWordEdge rule fine (fun index => (suffix index).1)) := by
    rw [decomposition, block_word_append_first_coordinates_completion,
      generation_word_edge_append_completion]
  apply zeros (path (coarse + fine + 2)) rfl
  rintro ⟨child, equality⟩
  rw [edgeIdentity] at equality
  exact generation_block_cell_edge_disjoint_completion rule coarse fine
    (generationWordEdge rule coarse parentEdges) (generationWordEdge rule coarse (fun index => (path (coarse + 1) index).1))
    (Ne.symm differentEdges) child (generationWordEdge rule fine (fun index => (suffix index).1)) equality

include stationary retainedPaths convergence in
theorem actual_parent_binary_cutoff_pushforward_square_integral_completion
    [IsProbabilityMeasure boundaryLaw]
    [CompactSpace (UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)))]
    (realizationMeasurable : Measurable realization)
    (coarse fine : ℕ) (parentEdges : Fin (coarse + 1) → Fin rule.edges)
    (selected : Finset (Fin (rule.generation (coarse + fine + 1)).vertices))
    (internal : ∀ vertex ∈ selected, ∃ inside : (rule.generation fine).network.InteriorVertex,
      (generationBlockCellEmbedding rule coarse fine (generationWordEdge rule coarse parentEdges)).vertex inside.val = vertex) :
    (∫ point, actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
      (coarse + fine + 1) (fun vertex => if vertex ∈ selected then 1 else 0) point^2 ∂(boundaryLaw.map realization)) ≤
      boundaryLaw.real (physicalSocketCylinderCompletion rule (coarse + 1) parentEdges) := by
  classical
  have zeroOutside := actual_parent_binary_cutoff_realization_zero_completion rule p positive belowOne fixedPoint growth value
    growthPositive marks stationary boundaryLaw retainedPaths realization convergence coarse fine parentEdges selected internal
  have range := actual_harmonic_completion_unit_interval_completion rule p positive belowOne fixedPoint growth value growthPositive
    marks stationary (coarse + fine + 1) (fun vertex => if vertex ∈ selected then 1 else 0)
    (fun vertex _ => by by_cases member : vertex ∈ selected <;> simp [member])
  have comparison : ∀ᵐ path ∂boundaryLaw,
      actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
        (coarse + fine + 1) (fun vertex => if vertex ∈ selected then 1 else 0) (realization path)^2 ≤
      (physicalSocketCylinderCompletion rule (coarse + 1) parentEdges).indicator (fun _ => (1 : ℝ)) path := by
    filter_upwards [zeroOutside] with path vanishes
    by_cases member : path ∈ physicalSocketCylinderCompletion rule (coarse + 1) parentEdges
    · rw [Set.indicator_of_mem member]
      obtain ⟨nonnegative, below⟩ := range (realization path)
      nlinarith
    · rw [Set.indicator_of_notMem member, vanishes member]
      norm_num
  have squaredContinuous : Continuous (fun point : ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value
      growthPositive ⟨marks.val, marks.property.1.1⟩ =>
      actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive
        marks (coarse + fine + 1) (fun vertex => if vertex ∈ selected then 1 else 0) point^2) :=
    (actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive
      marks (coarse + fine + 1) (fun vertex => if vertex ∈ selected then 1 else 0)).continuous.pow 2
  have transport := integral_map_of_stronglyMeasurable (μ := boundaryLaw) realizationMeasurable squaredContinuous.stronglyMeasurable
  rw [transport]
  have squaredMeasurable := (squaredContinuous.measurable.comp realizationMeasurable).aestronglyMeasurable (μ := boundaryLaw)
  have squaredIntegrable : Integrable (fun path =>
      actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks
        (coarse + fine + 1) (fun vertex => if vertex ∈ selected then 1 else 0) (realization path)^2) boundaryLaw := by
    apply Integrable.mono' (integrable_const (1 : ℝ)) squaredMeasurable
    exact Eventually.of_forall (fun path => by
      dsimp only [Function.comp_def] at ⊢
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      obtain ⟨nonnegative, below⟩ := range (realization path)
      nlinarith)
  have bounded := integral_mono_ae squaredIntegrable
    ((integrable_const (1 : ℝ)).indicator (physical_socket_cylinder_measurable_completion rule _ _)) comparison
  rw [integral_indicator (physical_socket_cylinder_measurable_completion rule _ _)] at bounded
  simpa only [setIntegral_const, smul_eq_mul, mul_one] using bounded

end
end IGSIII34.Spectral
