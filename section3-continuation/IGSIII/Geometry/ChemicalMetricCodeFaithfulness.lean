import IGSIII.Geometry.ActualChemicalSkeleton
import IGSIII.Geometry.CellLocalisationMetricCode
import IGSIII.Chemical.SmallBall.CodedMetricMeasureUniqueness

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution Filter
open scoped Topology ENNReal

/-- A fixed countable label type, independent of the retained configuration. -/
def ChemicalVertexLabel (rule : Rule) := Σ depth, Fin (rule.generation depth).vertices

instance chemicalVertexLabelCountable (rule : Rule) : Countable (ChemicalVertexLabel rule) :=
  inferInstanceAs (Countable (Σ depth, Fin (rule.generation depth).vertices))

/-- Retained labels name their original vertex; every other label names the
source at its own finite level. Thus no configuration-dependent label type is
needed to represent the actual random completion. -/
def chemicalRetainedLabelVertex (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges) (label : ChemicalVertexLabel rule) :
    RetainedSkeletonVertex (rule.generation label.1).network (configuration label.1) := by
  classical
  exact if reachable : ((rule.generation label.1).network.openGraph (configuration label.1)).Reachable
      (rule.generation label.1).network.source label.2 then ⟨label.2, reachable⟩
    else ⟨(rule.generation label.1).network.source, SimpleGraph.Reachable.refl _⟩

theorem chemicalRetainedLabelVertex_of_retained (rule : Rule)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges) (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    chemicalRetainedLabelVertex rule configuration ⟨depth, vertex.val⟩ = vertex := by
  classical
  simp only [chemicalRetainedLabelVertex, dif_pos vertex.property]
  rfl

theorem chemicalRetainedLabelVertex_val_congr (rule : Rule)
    (firstConfiguration lastConfiguration : ∀ depth, Configuration (rule.generation depth).edges)
    (configurationEquality : firstConfiguration = lastConfiguration) (label : ChemicalVertexLabel rule) :
    (chemicalRetainedLabelVertex rule firstConfiguration label).val =
      (chemicalRetainedLabelVertex rule lastConfiguration label).val := by
  cases configurationEquality
  rfl

variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (scale : ℝ) (scalePositive : 0 < scale)
variable (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
variable (positive : ∀ depth edge, configuration depth edge = true → 0 < lengths depth edge)
variable (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    scale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))

/-- Fixed total labels in the actual chemical completion. -/
def actualChemicalLabelPoint (label : ChemicalVertexLabel rule) :
    ActualChemicalSpace rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence :=
  actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence
    label.1 (chemicalRetainedLabelVertex rule configuration label)

theorem actualChemicalLabelPoint_of_retained (depth : ℕ)
    (vertex : RetainedSkeletonVertex (rule.generation depth).network (configuration depth)) :
    actualChemicalLabelPoint rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence
      ⟨depth, vertex.val⟩ =
    actualChemicalVertex rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence depth vertex := by
  unfold actualChemicalLabelPoint
  rw [chemicalRetainedLabelVertex_of_retained]

/-- The fixed labels contain every actual finite retained vertex, so their
range is dense in the actual completion. -/
theorem actualChemicalLabelPoint_denseRange :
    DenseRange (actualChemicalLabelPoint rule classicalRule configuration coherent scale scalePositive
      lengths nonnegative positive childConvergence) := by
  apply (actualChemicalVertex_dense rule classicalRule configuration coherent scale scalePositive
    lengths nonnegative positive childConvergence).mono
  intro point membership
  obtain ⟨depth, vertex, rfl⟩ := Set.mem_iUnion.mp membership
  exact ⟨⟨depth, vertex.val⟩, actualChemicalLabelPoint_of_retained rule classicalRule configuration coherent
    scale scalePositive lengths nonnegative positive childConvergence depth vertex⟩

/-- Every cross-generation label distance is an original finite pair distance
at the common persistent level; no limiting distance is inserted as data. -/
theorem actualChemicalLabelPoint_distance (first last : ChemicalVertexLabel rule) :
    dist (actualChemicalLabelPoint rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence first)
      (actualChemicalLabelPoint rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence last) =
    weightedDistance ((rule.generation (max first.1 last.1)).network.openGraph (configuration (max first.1 last.1)))
      (indexedBondCost (rule.generation (max first.1 last.1)).network (lengths (max first.1 last.1)))
      (persistentVertexEmbedding rule first.1 (max first.1 last.1) (le_max_left _ _)
        (chemicalRetainedLabelVertex rule configuration first).val)
      (persistentVertexEmbedding rule last.1 (max first.1 last.1) (le_max_right _ _)
        (chemicalRetainedLabelVertex rule configuration last).val) := by
  unfold actualChemicalLabelPoint
  rw [actualChemicalVertex_persistent rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence
    first.1 (max first.1 last.1) (le_max_left _ _) (chemicalRetainedLabelVertex rule configuration first),
    actualChemicalVertex_persistent rule classicalRule configuration coherent scale scalePositive lengths nonnegative positive childConvergence
    last.1 (max first.1 last.1) (le_max_right _ _) (chemicalRetainedLabelVertex rule configuration last),
    actualChemicalVertex_distance]
  rfl
section ActualCriticalCode
open MeasureTheory
variable (p : ℝ) (probabilityPositive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
variable (growth amplitude : ℝ) (growthPositive : 0 < growth)
variable (value : Lp ℝ 2 (independentInnovationLaw rule p probabilityPositive belowOne fixedPoint))
variable (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
variable (markedCoherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
variable (lengthNonnegative : ∀ depth edge, 0 ≤ chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks depth edge)
variable (lengthPositive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true →
  0 < chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks depth edge)
variable (lengthConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    growth ^ (coarse + fine + 2)) atTop
      (𝓝 (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks coarse edge)))

/-- The actual cross-level distance is a specified coordinate of the given
chemical metric code, after the deterministic retention and persistence maps. -/
theorem actualChemicalLabelPoint_distance_code (first last : ChemicalVertexLabel rule) :
    dist (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) markedCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive lengthConvergence first)
      (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) markedCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive lengthConvergence last) =
    (chemicalMetricCode rule p probabilityPositive belowOne fixedPoint growth amplitude value marks).2 true (max first.1 last.1)
      (persistentVertexEmbedding rule first.1 (max first.1 last.1) (le_max_left _ _)
        (chemicalRetainedLabelVertex rule (fun depth => markedGenerationConfiguration rule marks depth [] true) first).val)
      (persistentVertexEmbedding rule last.1 (max first.1 last.1) (le_max_right _ _)
        (chemicalRetainedLabelVertex rule (fun depth => markedGenerationConfiguration rule marks depth [] true) last).val) :=
  (actualChemicalLabelPoint_distance rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) markedCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive lengthConvergence first last).trans
    (chemicalMetricCode_root_distance rule classicalRule p probabilityPositive belowOne fixedPoint growth amplitude value marks
      (max first.1 last.1) _ _).symm

variable (lastMarks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
variable (lastCoherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true))
variable (lastNonnegative : ∀ depth edge, 0 ≤ chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks depth edge)
variable (lastPositive : ∀ depth edge, markedGenerationConfiguration rule lastMarks depth [] true edge = true →
  0 < chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks depth edge)
variable (lastConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (markedGenerationConfiguration rule lastMarks (coarse + fine + 1) [] true) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    growth ^ (coarse + fine + 2)) atTop
      (𝓝 (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks coarse edge)))

/-- Equality of the actual code gives every cross-generation label distance
in two actual completed clusters. Retention and distances are recovered from
the code itself, rather than assumed as a faithfulness certificate. -/
theorem actualChemicalLabelPoint_distances_eq_of_code_eq
    (codeEquality : chemicalMetricCode rule p probabilityPositive belowOne fixedPoint growth amplitude value marks =
      chemicalMetricCode rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks)
    (first last : ChemicalVertexLabel rule) :
    dist (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) markedCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive lengthConvergence first)
      (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) markedCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive lengthConvergence last) =
    dist (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) lastCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks)
      lastNonnegative lastPositive lastConvergence first)
      (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) lastCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks)
      lastNonnegative lastPositive lastConvergence last) := by
  have configurationEquality : (fun depth => markedGenerationConfiguration rule marks depth [] true) =
      (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) := by
    funext depth
    exact congrArg (fun code : ChemicalMetricCode rule => code.1 true depth) codeEquality
  rw [actualChemicalLabelPoint_distance_code rule classicalRule p probabilityPositive belowOne fixedPoint growth amplitude growthPositive
    value marks markedCoherent lengthNonnegative lengthPositive lengthConvergence,
    actualChemicalLabelPoint_distance_code rule classicalRule p probabilityPositive belowOne fixedPoint growth amplitude growthPositive
    value lastMarks lastCoherent lastNonnegative lastPositive lastConvergence]
  rw [chemicalRetainedLabelVertex_val_congr rule _ _ configurationEquality first,
    chemicalRetainedLabelVertex_val_congr rule _ _ configurationEquality last]
  exact congrArg (fun code : ChemicalMetricCode rule => code.2 true (max first.1 last.1)
    (persistentVertexEmbedding rule first.1 (max first.1 last.1) (le_max_left _ _)
      (chemicalRetainedLabelVertex rule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) first).val)
    (persistentVertexEmbedding rule last.1 (max first.1 last.1) (le_max_right _ _)
      (chemicalRetainedLabelVertex rule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) last).val)) codeEquality

/-- Equal actual metric codes determine the actual completed clusters up to
an isometry that preserves every original retained vertex label, and hence
the ordered terminal labels whenever crossing holds. -/
theorem exists_actualChemicalLabelIsometryEquiv_of_code_eq
    (codeEquality : chemicalMetricCode rule p probabilityPositive belowOne fixedPoint growth amplitude value marks =
      chemicalMetricCode rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks) :
    ∃ equivalence : ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) markedCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive lengthConvergence ≃ᵢ ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) lastCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks)
      lastNonnegative lastPositive lastConvergence,
      ∀ label : ChemicalVertexLabel rule,
        equivalence (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) markedCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive lengthConvergence label) = actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) lastCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks)
      lastNonnegative lastPositive lastConvergence label :=
  exists_isometryEquiv_of_dense_labels
    (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) markedCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive lengthConvergence)
    (actualChemicalLabelPoint rule classicalRule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) lastCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks)
      lastNonnegative lastPositive lastConvergence)
    (actualChemicalLabelPoint_denseRange rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true) markedCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value marks)
      lengthNonnegative lengthPositive lengthConvergence)
    (actualChemicalLabelPoint_denseRange rule classicalRule (fun depth => markedGenerationConfiguration rule lastMarks depth [] true) lastCoherent growth growthPositive
      (chemicalBlockLimitLength rule p probabilityPositive belowOne fixedPoint growth amplitude value lastMarks)
      lastNonnegative lastPositive lastConvergence)
    (actualChemicalLabelPoint_distances_eq_of_code_eq rule classicalRule p probabilityPositive belowOne fixedPoint
      growth amplitude growthPositive value marks markedCoherent lengthNonnegative lengthPositive lengthConvergence
      lastMarks lastCoherent lastNonnegative lastPositive lastConvergence codeEquality)
end ActualCriticalCode
end
end IGSIII.Geometry


