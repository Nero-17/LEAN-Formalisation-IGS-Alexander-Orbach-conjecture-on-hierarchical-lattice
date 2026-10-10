import IGSIII34.Percolation.ActualSubstitution
import IGSIII34.Percolation.NetworkEquivalence
import IGSIII.Chemical.SubstitutionPaths.IndependentInnovations
import IGSIII.Probability.IndependentTreeChildren

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Percolation
noncomputable section
open Resistance Resistance.FiniteNetwork
open Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution
open IGSIII.Probability MeasureTheory ProbabilityTheory

def electricalCell {vertices edges : ℕ} (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (input : Fin edges → ℝ) : ℝ :=
  (network rule configuration).effectiveResistance (fun edge => input edge.val)

def unitConfigurationResistance {vertices edges : ℕ} (rule : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) : ℝ := electricalCell rule configuration (fun _ => 1)

theorem generation_unitResistance_recursion (rule : Rule) (depth : ℕ)
    (fine : Configuration (rule.generation (depth + 1)).edges)
    (crosses : (rule.generation (depth + 1)).network.crosses fine = true) :
    unitConfigurationResistance (rule.generation (depth + 1)).network fine =
      electricalCell rule.network (generationRootConfiguration rule depth fine)
        (fun edge => unitConfigurationResistance (rule.generation depth).network
          (generationTopCells rule depth fine edge)) := by
  have coarseCrosses : rule.network.crosses (generationRootConfiguration rule depth fine) = true :=
    (generation_root_crosses rule depth fine).trans crosses
  have relabel := networkEquivalence_resistance (rule.generationTopDecomposition depth) fine crosses
    (fun _ => 1) (fun _ => by norm_num)
  rw [← configuration_of_topCells rule depth fine] at relabel
  have recursion := actual_substitution_resistance rule.network (rule.generation depth).network
    (generationTopCells rule depth fine) coarseCrosses (fun _ => 1) (fun _ => by norm_num)
  exact relabel.symm.trans recursion

def electricalIteration (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    ℕ → List (Fin rule.edges) → ℝ
  | 0, _ => 1
  | depth + 1, address => electricalCell rule.network (marks (address, true))
      (fun edge => electricalIteration rule marks depth (address ++ [edge]))

theorem markedGeneration_resistance_eq_iteration (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    unitConfigurationResistance (rule.generation depth).network
        (markedGenerationConfiguration rule marks depth address true) =
      electricalIteration rule marks (depth + 1) address := by
  induction depth generalizing address with
  | zero => rfl
  | succ depth inductionHypothesis =>
      rw [generation_unitResistance_recursion rule depth _
        (markedGenerationConfiguration_crosses rule marks crossing (depth + 1) address true)]
      rw [markedGenerationConfiguration_root rule marks crossing,
        markedGenerationConfiguration_topCells]
      unfold electricalCell
      congr 1
      funext edge
      have retained : marks (address, true) edge.val = true := edge.property
      simpa only [retained] using inductionHypothesis (address ++ [edge.val])

theorem electricalIteration_positive (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address, rule.network.crosses (marks (address, true)) = true)
    (depth : ℕ) (address : List (Fin rule.edges)) :
    0 < electricalIteration rule marks depth address := by
  induction depth generalizing address with
  | zero => norm_num [electricalIteration]
  | succ depth inductionHypothesis =>
      exact (network rule.network (marks (address, true))).effectiveResistance_pos_of_connected
        (connected_of_crosses _ _ (crossing address))
        (fun edge => inductionHypothesis (address ++ [edge.val]))

theorem electricalIteration_shift (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (addressPrefix address : List (Fin rule.edges)) :
    electricalIteration rule (innovationTreeShift rule addressPrefix marks) depth address =
      electricalIteration rule marks depth (addressPrefix ++ address) := by
  induction depth generalizing address with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [electricalIteration, innovationTreeShift, inductionHypothesis, List.append_assoc]

end
end IGSIII34.Percolation
