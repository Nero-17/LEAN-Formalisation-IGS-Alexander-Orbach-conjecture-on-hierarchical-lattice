import IGSIII.Chemical.SmallBall.ActualChemicalTerminals

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution IGSIII.Geometry Filter
open scoped ENNReal Topology

noncomputable section

variable (rule : Rule) (classicalRule : rule.Classical)
variable (configuration : ∀ depth, Configuration (rule.generation depth).edges)
variable (coherent : configurationSequenceCoherent rule configuration)
variable (crossing : ∀ depth, (rule.generation depth).network.crosses (configuration depth) = true)
variable (growth : ℝ) (growthPositive : 0 < growth)
variable (limitLength : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
variable (lengthNonnegative : ∀ depth edge, 0 ≤ limitLength depth edge)
variable (lengthPositive : ∀ depth edge, configuration depth edge = true → 0 < limitLength depth edge)
variable (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
  (((rule.generation fine).network.openGraph
    (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
    growth ^ (coarse + fine + 2)) atTop (𝓝 (limitLength coarse edge)))

theorem actualChemicalTerminal_distance_eq_field
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (amplitude : ℝ) (value : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configurationIdentity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (fieldConvergence : Tendsto (fun depth => (markedTerminalDistance rule marks depth [] true : ℝ) / growth ^ (depth + 1))
      atTop (𝓝 (amplitude * chemicalField rule p positive lessOne fixedPoint value [] marks))) :
    dist (actualChemicalTerminal rule classicalRule configuration coherent crossing growth growthPositive limitLength lengthNonnegative lengthPositive
        childConvergence true)
      (actualChemicalTerminal rule classicalRule configuration coherent crossing growth growthPositive limitLength lengthNonnegative lengthPositive
        childConvergence false) = amplitude * chemicalField rule p positive lessOne fixedPoint value [] marks := by
  apply actualChemicalTerminal_distance_of_terminal_convergence
  apply fieldConvergence.congr'
  apply Eventually.of_forall
  intro depth
  dsimp only
  rw [configurationIdentity depth]
  rfl

theorem actualChemicalTerminal_distance_positive
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (amplitude : ℝ) (amplitudePositive : 0 < amplitude)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configurationIdentity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (fieldPositive : 0 < chemicalField rule p positive lessOne fixedPoint value [] marks)
    (fieldConvergence : Tendsto (fun depth => (markedTerminalDistance rule marks depth [] true : ℝ) / growth ^ (depth + 1))
      atTop (𝓝 (amplitude * chemicalField rule p positive lessOne fixedPoint value [] marks))) :
    0 < dist (actualChemicalTerminal rule classicalRule configuration coherent crossing growth growthPositive limitLength lengthNonnegative lengthPositive
        childConvergence true)
      (actualChemicalTerminal rule classicalRule configuration coherent crossing growth growthPositive limitLength lengthNonnegative lengthPositive
        childConvergence false) := by
  rw [actualChemicalTerminal_distance_eq_field rule classicalRule configuration coherent crossing growth growthPositive limitLength
    lengthNonnegative lengthPositive childConvergence p positive lessOne fixedPoint amplitude value marks configurationIdentity fieldConvergence]
  exact mul_pos amplitudePositive fieldPositive

theorem actualChemicalTerminal_distinct
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (amplitude : ℝ) (amplitudePositive : 0 < amplitude)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive lessOne fixedPoint))
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (configurationIdentity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] true)
    (fieldPositive : 0 < chemicalField rule p positive lessOne fixedPoint value [] marks)
    (fieldConvergence : Tendsto (fun depth => (markedTerminalDistance rule marks depth [] true : ℝ) / growth ^ (depth + 1))
      atTop (𝓝 (amplitude * chemicalField rule p positive lessOne fixedPoint value [] marks))) :
    actualChemicalTerminal rule classicalRule configuration coherent crossing growth growthPositive limitLength lengthNonnegative lengthPositive
        childConvergence true ≠
      actualChemicalTerminal rule classicalRule configuration coherent crossing growth growthPositive limitLength lengthNonnegative lengthPositive
        childConvergence false :=
  dist_pos.mp (actualChemicalTerminal_distance_positive rule classicalRule configuration coherent crossing growth growthPositive limitLength
    lengthNonnegative lengthPositive childConvergence p positive lessOne fixedPoint amplitude amplitudePositive value marks
    configurationIdentity fieldPositive fieldConvergence)

end
end IGSIII.Chemical.SmallBall