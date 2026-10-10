import IGSIII34.Resistance.Minimizer
import IGSIII34.Resistance.StrictImprovement
import Mathlib.LinearAlgebra.Basis.VectorSpace

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork

noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem energy_eq_zero_iff {resistance current : Edge → ℝ}
    (positive : ∀ edge, 0 < resistance edge) :
    energy resistance current = 0 ↔ ∀ edge, current edge = 0 := by
  constructor
  · intro zeroEnergy edge
    have termBelow := Finset.single_le_sum (fun index _ =>
      mul_nonneg (positive index).le (sq_nonneg (current index))) (Finset.mem_univ edge)
    change resistance edge * current edge ^ 2 ≤ energy resistance current at termBelow
    rw [zeroEnergy] at termBelow
    have squareZero : current edge ^ 2 = 0 := by
      nlinarith [sq_nonneg (current edge), positive edge]
    exact sq_eq_zero_iff.mp squareZero
  · intro zeroCurrent
    simp [energy, zeroCurrent]

theorem minimizing_current_orthogonal (network : FiniteNetwork Vertex Edge)
    {resistance current perturbation : Edge → ℝ}
    (positive : ∀ edge, 0 < resistance edge)
    (unitFlow : current ∈ network.unitFlows)
    (minimal : energy resistance current = network.effectiveResistance resistance)
    (zeroDivergence : ∀ vertex, network.divergence perturbation vertex = 0) :
    crossEnergy resistance current perturbation = 0 := by
  have directionNonnegative := energy_nonneg (fun edge => (positive edge).le) perturbation
  by_cases zeroEnergy : energy resistance perturbation = 0
  · have zeroCurrent := (energy_eq_zero_iff positive).mp zeroEnergy
    simp [crossEnergy, zeroCurrent]
  · have directionPositive : 0 < energy resistance perturbation :=
      lt_of_le_of_ne directionNonnegative (Ne.symm zeroEnergy)
    by_contra nonzeroCross
    rcases lt_or_gt_of_ne nonzeroCross with negative | positiveCross
    · have improvement := network.resistance_strictly_below_trial_of_descent
        (fun edge => (positive edge).le) unitFlow zeroDivergence negative directionPositive
      rw [minimal] at improvement
      exact (lt_irrefl _ improvement)
    · have negDivergence : ∀ vertex,
          network.divergence (fun edge => -perturbation edge) vertex = 0 := by
        intro vertex
        rw [network.divergence_neg, zeroDivergence, neg_zero]
      have negCross : crossEnergy resistance current (fun edge => -perturbation edge) =
          -crossEnergy resistance current perturbation := by
        simp [crossEnergy, Finset.sum_neg_distrib]
      have negEnergy : energy resistance (fun edge => -perturbation edge) =
          energy resistance perturbation := by simp [energy]
      have improvement := network.resistance_strictly_below_trial_of_descent
        (fun edge => (positive edge).le) unitFlow negDivergence
        (by rw [negCross]; linarith) (by rw [negEnergy]; exact directionPositive)
      rw [minimal] at improvement
      exact (lt_irrefl _ improvement)

end
end IGSIII34.Resistance.FiniteNetwork

#check LinearMap.quotKerEquivRange
#check LinearMap.quotKerEquivOfSurjective
#check LinearMap.rangeRestrict
#check LinearMap.liftQ
#check LinearMap.exists_extend
#check LinearMap.ker_le_ker_iff
#check LinearMap.liftOfKerLE
#check LinearMap.pi
#check LinearMap.proj
#check Pi.single
#check LinearMap.map_sum
