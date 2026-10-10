import IGSIII.Geometry.BoxDimensionCellPacking
import IGSIII.Geometry.CriticalChemicalLengths
import IGSIII.Chemical.SmallBall.ActualGoodCylinderPopulation

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall
open IGSIII.Probability MeasureTheory Filter
open scoped Topology NNReal ENNReal

variable (rule : Rule) (classicalRule : rule.Classical)
variable (p : ℝ) (probability_positive : 0 < p) (below_one : p < 1)
variable (fixed_point : rule.network.reliability p = p)
variable (growth amplitude : ℝ) (growth_positive : 0 < growth) (amplitude_positive : 0 < amplitude)
variable (value : Lp ℝ 2 (independentInnovationLaw rule p probability_positive below_one fixed_point))
variable (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
variable (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
variable (length_nonnegative : ∀ coarse edge,
  0 ≤ chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks coarse edge)
variable (length_positive : ∀ coarse edge, markedGenerationConfiguration rule marks coarse [] true edge = true →
  0 < chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks coarse edge)
variable (child_convergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    growth ^ (coarse + fine + 2)) atTop
      (𝓝 (chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks coarse edge)))

/-- Positive actual child fields give a genuine finite packing at the
chemical scale, using the actual good connected cylinders on this mark sample. -/
theorem actual_good_cylinders_le_coveringNumber (threshold : ℝ) (threshold_positive : 0 < threshold) (depth : ℕ) :
    ((goodConnectedCylinderIndices rule (positiveFieldGoodEvent rule value threshold) depth marks).card : ℕ∞) ≤
      Metric.coveringNumber
        ⟨(amplitude * threshold / growth ^ (depth + 2)) / 2, (by positivity : 0 ≤ (amplitude * threshold / growth ^ (depth + 2)) / 2)⟩
        (Set.univ : Set (ActualChemicalSpace rule classicalRule
          (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growth_positive
          (chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks)
          length_nonnegative length_positive child_convergence)) := by
  classical
  let indices := goodConnectedCylinderIndices rule (positiveFieldGoodEvent rule value threshold) depth marks
  let indexEmbedding : {edge // edge ∈ indices} ↪ Fin (rule.generation depth).edges :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have membership (index : {edge // edge ∈ indices}) :=
    (goodConnectedCylinderIndices_mem rule (positiveFieldGoodEvent rule value threshold) depth marks index.val).mp index.property
  have retained (index : {edge // edge ∈ indices}) :=
    ((rule.generation depth).network.childState_connected_iff .connected _ index.val).mp (membership index).1
  have attached (index : {edge // edge ∈ indices}) :
      ((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth [] true)).Reachable
        (rule.generation depth).network.source ((rule.generation depth).network.endpoint index.val).1 := by
    simpa only [active, show (LiveState.connected == LiveState.both) = false from rfl,
      Bool.false_and, Bool.or_false, SimpleGraph.reachableDecide_eq_true] using (retained index).2
  have floor_bound (index : {edge // edge ∈ indices}) (child : Fin rule.edges)
      (opened : markedGenerationConfiguration rule marks (depth + 1) [] true (finProdFinEquiv (index.val, child)) = true) :
      amplitude * threshold / growth ^ (depth + 2) ≤
        chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks (depth + 1)
          (finProdFinEquiv (index.val, child)) := by
    have good_bound := (membership index).2 child
    change threshold ≤ value (innovationTreeShift rule [child]
      (innovationTreeShift rule (generationEdgeAddress rule depth index.val) marks)) at good_bound
    rw [innovationTreeShift_append] at good_bound
    simp only [chemicalBlockLimitLength, opened, ↓reduceIte, generationEdgeAddress_bottom]
    change amplitude * threshold / growth ^ (depth + 2) ≤
      amplitude * value (innovationTreeShift rule (generationEdgeAddress rule depth index.val ++ [child]) marks) /
        growth ^ (depth + 2)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left good_bound amplitude_positive.le)
      (pow_pos growth_positive _).le
  have packing := actualChemicalSpace_packing_of_connected_cells rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growth_positive
    (chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks)
    length_nonnegative length_positive child_convergence depth indexEmbedding
    (fun index => (retained index).1) attached (amplitude * threshold / growth ^ (depth + 2))
    (by positivity) floor_bound
  simpa only [indices, Fintype.card_coe] using packing

/-- The packing radius in a fixed geometric progression, with the exact
same growth as the actual terminal field. -/
theorem actual_good_cylinders_le_geometric_coveringNumber
    (threshold : ℝ) (threshold_positive : 0 < threshold) (depth : ℕ) :
    ((goodConnectedCylinderIndices rule (positiveFieldGoodEvent rule value threshold) depth marks).card : ℕ∞) ≤
      Metric.coveringNumber
        ((⟨amplitude * threshold / (2 * growth ^ 2), by positivity⟩ : ℝ≥0) *
          (⟨growth⁻¹, inv_nonneg.mpr growth_positive.le⟩ : ℝ≥0) ^ depth)
        (Set.univ : Set (ActualChemicalSpace rule classicalRule
          (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent growth growth_positive
          (chemicalBlockLimitLength rule p probability_positive below_one fixed_point growth amplitude value marks)
          length_nonnegative length_positive child_convergence)) := by
  have radius_identity : (amplitude * threshold / growth ^ (depth + 2)) / 2 =
      (amplitude * threshold / (2 * growth ^ 2)) * (growth⁻¹) ^ depth := by
    rw [pow_add, inv_pow]
    field_simp
  have radius_equality :
      (⟨(amplitude * threshold / growth ^ (depth + 2)) / 2, (by positivity : 0 ≤ (amplitude * threshold / growth ^ (depth + 2)) / 2)⟩ : ℝ≥0) =
        (⟨amplitude * threshold / (2 * growth ^ 2), by positivity⟩ : ℝ≥0) *
          (⟨growth⁻¹, inv_nonneg.mpr growth_positive.le⟩ : ℝ≥0) ^ depth := by
    apply NNReal.eq
    exact radius_identity
  rw [← radius_equality]
  exact actual_good_cylinders_le_coveringNumber rule classicalRule p probability_positive below_one fixed_point
    growth amplitude growth_positive amplitude_positive value marks coherent length_nonnegative length_positive child_convergence
    threshold threshold_positive depth
end
end IGSIII.Geometry



