import IGSIII.Geometry.RootedComponentInclusion
import IGSIII.Geometry.CriticalChemicalLengths

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution MeasureTheory Filter
open scoped Topology ENNReal

/-- The intrinsic connected child lengths of an actual component. Its raw
innovation and planted mask remain unchanged, and the offset uses root units. -/
def chemicalAddressBlockLimitLength (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges)) (opened : Bool) (offset coarse : ℕ) (edge : Fin (rule.generation coarse).edges) : ℝ :=
  if markedGenerationConfiguration rule marks coarse address opened edge then
    amplitude * chemicalField rule p positive belowOne fixedPoint value (address ++ generationEdgeAddress rule coarse edge) marks /
      growth ^ (coarse + 1 + offset)
  else 0

theorem address_block_lengths_of_terminal_field
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth amplitude : ℝ)
    (growthPositive : 0 < growth) (amplitudePositive : 0 < amplitude)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fieldPositive : ∀ address, 0 < chemicalField rule p positive belowOne fixedPoint value address marks)
    (fieldConvergence : ∀ address, Tendsto
      (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
      atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks)))
    (address : List (Fin rule.edges)) (opened : Bool) (offset : ℕ) :
    (∀ coarse edge, 0 ≤ chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks address opened offset coarse edge) ∧
    (∀ coarse edge, markedGenerationConfiguration rule marks coarse address opened edge = true →
      0 < chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks address opened offset coarse edge) ∧
    (∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) address opened) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        growth ^ (coarse + fine + 2 + offset)) atTop
      (𝓝 (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks address opened offset coarse edge))) := by
  have lengthPositive (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) :
      0 < amplitude * chemicalField rule p positive belowOne fixedPoint value (address ++ generationEdgeAddress rule coarse edge) marks /
        growth ^ (coarse + 1 + offset) := div_pos (mul_pos amplitudePositive (fieldPositive _)) (pow_pos growthPositive _)
  refine ⟨?_, ?_, ?_⟩
  · intro coarse edge
    unfold chemicalAddressBlockLimitLength
    split
    · exact (lengthPositive coarse edge).le
    · exact le_refl 0
  · intro coarse edge retained
    simpa only [chemicalAddressBlockLimitLength, retained, ↓reduceIte] using lengthPositive coarse edge
  · intro coarse edge
    simp only [generationBlockCells_marked]
    cases state : markedGenerationConfiguration rule marks coarse address opened edge with
    | false =>
      simp only [state, chemicalAddressBlockLimitLength, Bool.false_eq_true, ↓reduceIte]
      have zeroSequence : (fun fine =>
          (((rule.generation fine).network.openGraph
            (markedGenerationConfiguration rule marks fine (address ++ generationEdgeAddress rule coarse edge) false)).dist
              (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
            growth ^ (coarse + fine + 2 + offset)) = fun _ : ℕ => (0 : ℝ) := by
        funext fine
        change (markedTerminalDistance rule marks fine (address ++ generationEdgeAddress rule coarse edge) false : ℝ) / _ = _
        rw [markedTerminalDistance_noncrossing rule marks crossing, Nat.cast_zero, zero_div]
      rw [zeroSequence]
      exact tendsto_const_nhds
    | true =>
      simp only [state, chemicalAddressBlockLimitLength, ↓reduceIte]
      have convergence := (fieldConvergence (address ++ generationEdgeAddress rule coarse edge)).div_const (growth ^ (coarse + 1 + offset))
      convert convergence using 1
      funext fine
      change (markedTerminalDistance rule marks fine (address ++ generationEdgeAddress rule coarse edge) true : ℝ) /
        growth ^ (coarse + fine + 2 + offset) = _
      rw [show coarse + fine + 2 + offset = (fine + 1) + (coarse + 1 + offset) by omega, pow_add, div_div]

theorem actual_component_block_lengths
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth amplitude : ℝ)
    (growthPositive : 0 < growth) (amplitudePositive : 0 < amplitude)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fieldPositive : ∀ address, 0 < chemicalField rule p positive belowOne fixedPoint value address marks)
    (fieldConvergence : ∀ address, Tendsto
      (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
      atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks)))
    (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) :
    let componentConfiguration := fun fine => generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge
    let componentLengths := chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks
      (generationEdgeAddress rule coarse edge) (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1)
    (∀ fine child, 0 ≤ componentLengths fine child) ∧
    (∀ fine child, componentConfiguration fine child = true → 0 < componentLengths fine child) ∧
    (∀ age child, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule age fine (componentConfiguration (age + fine + 1)) child)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        growth ^ (age + fine + 2 + (coarse + 1))) atTop (𝓝 (componentLengths age child))) := by
  have identity (fine : ℕ) := generationBlockCells_marked rule marks coarse fine [] true edge
  simp only [List.nil_append] at identity
  simpa only [identity] using address_block_lengths_of_terminal_field rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive
    value marks crossing fieldPositive fieldConvergence (generationEdgeAddress rule coarse edge)
    (markedGenerationConfiguration rule marks coarse [] true edge) (coarse + 1)

end
end IGSIII.Geometry
