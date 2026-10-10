import IGSIII.Chemical.ChemicalScalar
import IGSIII.Chemical.SubstitutionPaths.BlockAddresses
import IGSIII.Geometry.ActualCriticalMesh
import IGSIII.Probability.ExponentialGrowthUniqueness

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall MeasureTheory Filter
open scoped Topology ENNReal

/-- The actual limiting length of a coarse retained edge, in root units. -/
def chemicalBlockLimitLength (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth amplitude : ℝ)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) : ℝ :=
  if markedGenerationConfiguration rule marks coarse [] true edge then
    (amplitude * chemicalField rule p positive belowOne fixedPoint value (generationEdgeAddress rule coarse edge) marks) /
      growth ^ (coarse + 1)
  else 0

theorem actual_block_lengths_of_terminal_field
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth amplitude : ℝ)
    (growthPositive : 0 < growth) (amplitudePositive : 0 < amplitude)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (fieldPositive : ∀ address, 0 < chemicalField rule p positive belowOne fixedPoint value address marks)
    (fieldConvergence : ∀ address, Tendsto
      (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
      atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks))) :
    (∀ coarse edge, 0 ≤ chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks coarse edge) ∧
    (∀ coarse edge, markedGenerationConfiguration rule marks coarse [] true edge = true →
      0 < chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks coarse edge) ∧
    (∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        growth ^ (coarse + fine + 2)) atTop
      (𝓝 (chemicalBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks coarse edge))) := by
  have lengthPositive (coarse : ℕ) (edge : Fin (rule.generation coarse).edges) :
      0 < (amplitude * chemicalField rule p positive belowOne fixedPoint value (generationEdgeAddress rule coarse edge) marks) /
        growth ^ (coarse + 1) := div_pos (mul_pos amplitudePositive (fieldPositive _)) (pow_pos growthPositive _)
  refine ⟨?_, ?_, ?_⟩
  · intro coarse edge
    unfold chemicalBlockLimitLength
    split
    · exact (lengthPositive coarse edge).le
    · exact le_refl 0
  · intro coarse edge retained
    simpa only [chemicalBlockLimitLength, retained, ↓reduceIte] using lengthPositive coarse edge
  · intro coarse edge
    simp only [generationBlockCells_marked, List.nil_append]
    cases state : markedGenerationConfiguration rule marks coarse [] true edge with
    | false =>
      simp only [state, chemicalBlockLimitLength, Bool.false_eq_true, ↓reduceIte]
      have zeroDistance (fine : ℕ) := markedTerminalDistance_noncrossing rule marks crossing fine (generationEdgeAddress rule coarse edge)
      have zeroSequence : (fun fine =>
          (((rule.generation fine).network.openGraph
            (markedGenerationConfiguration rule marks fine (generationEdgeAddress rule coarse edge) false)).dist
              (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
            growth ^ (coarse + fine + 2)) = fun _ : ℕ => (0 : ℝ) := by
        funext fine
        change (markedTerminalDistance rule marks fine (generationEdgeAddress rule coarse edge) false : ℝ) / _ = _
        rw [zeroDistance, Nat.cast_zero, zero_div]
      rw [zeroSequence]
      exact tendsto_const_nhds
    | true =>
      simp only [state, chemicalBlockLimitLength, ↓reduceIte]
      have convergence := (fieldConvergence (generationEdgeAddress rule coarse edge)).div_const (growth ^ (coarse + 1))
      convert convergence using 1
      funext fine
      change (markedTerminalDistance rule marks fine (generationEdgeAddress rule coarse edge) true : ℝ) /
        growth ^ (coarse + fine + 2) = _
      rw [show coarse + fine + 2 = (fine + 1) + (coarse + 1) by omega, pow_add, div_div]

/-- The uniform mesh theorem uses the same unique chemical growth as any
actual scalar theorem satisfying the manuscript mean bounds. -/
theorem actual_critical_component_mesh_of_mean_bounds
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (eta : ℝ) (etaPositive : 0 < eta) (etaBelowOne : eta < 1) (productGreaterThanOne : 1 < growth * eta) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ start : ℕ, ∀ address opened depth, start ≤ address.length →
        (markedTerminalComponentRadius rule marks depth address opened : ℝ) / growth ^ (depth + 1 + address.length) ≤
          ((rule.edges + 1 : ℝ) / (1 - eta)) * eta ^ address.length := by
  obtain ⟨otherConstant, otherGrowth, _, _, growthLower, _, otherBounds, moments, terminalBound⟩ :=
    exists_actual_chemical_terminal_envelope rule classicalRule p positive belowOne fixedPoint
  have otherGrowthPositive : 0 < otherGrowth :=
    (show (0 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast Nat.zero_lt_of_lt classicalRule.scale).trans_le growthLower
  have growthIdentity := IGSIII.Probability.exponential_growth_unique (manuscriptDistanceMean rule p)
    growth otherGrowth constant⁻¹ otherConstant⁻¹ growthPositive otherGrowthPositive meanBounds otherBounds
  subst otherGrowth
  have growthGreaterThanOne : 1 < growth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le growthLower
  have largePower := (tendsto_pow_atTop_atTop_of_one_lt productGreaterThanOne).eventually (eventually_gt_atTop (rule.edges : ℝ))
  obtain ⟨power, powerPositive, momentGrowth⟩ := ((eventually_gt_atTop (0 : ℕ)).and largePower).exists
  obtain ⟨bound, boundFinite, momentBounds⟩ := moments (power : ℝ≥0∞) (by exact_mod_cast powerPositive) (by simp)
  exact ae_uniform_actual_component_mesh rule (independentInnovationLaw rule p positive belowOne fixedPoint)
    growth eta growthGreaterThanOne etaPositive etaBelowOne productGreaterThanOne.le power powerPositive momentGrowth
    (chemicalTerminalEnvelope rule p positive belowOne fixedPoint growth)
    (fun address opened => (momentBounds address opened).1.aestronglyMeasurable)
    bound boundFinite (fun address opened => (momentBounds address opened).2) terminalBound

end
end IGSIII.Geometry
