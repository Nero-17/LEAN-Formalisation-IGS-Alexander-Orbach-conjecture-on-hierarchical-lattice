import IGSIII.Chemical.ChemicalOmega
import IGSIII.Probability.Lp2Mean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory Filter
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped ENNReal Topology BigOperators

theorem chemicalOrbit_mean (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (growthNonnegative : 0 ≤ growth) (depth : ℕ) :
    (∫ marks, chemicalOrbit rule p positive belowOne fixedPoint growth depth marks
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) =
        manuscriptDistanceMean rule p depth / growth ^ depth := by
  cases depth with
  | zero =>
    change (∫ marks, chemicalUnitLp rule p positive belowOne fixedPoint 2 marks
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) = _
    rw [integral_congr_ae (chemicalUnitLp_ae rule p positive belowOne fixedPoint 2)]
    simp [manuscriptDistanceMean]
  | succ depth =>
    rw [chemicalOrbit_tail_eq_actual rule classical p positive belowOne fixedPoint growth growthNonnegative]
    rw [integral_congr_ae (markedObservableLp_ae rule p positive belowOne fixedPoint depth [] true
      (growthScaledDistance rule growth depth)),
      independentInnovationLaw_marked_observable]
    simp only [finiteMean, growthScaledDistance, manuscriptDistanceMean,
      conditionedDistanceMean, ← mul_div_assoc, ← Finset.sum_div]

theorem chemicalOmega_mean_atLeastOne (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (lowerMeans : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (membership : value ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth) :
    1 ≤ ∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint := by
  have meanCluster := membership.continuousAt_comp
    (lp2_mean_continuous (independentInnovationLaw rule p positive belowOne fixedPoint)).continuousAt
  apply (isClosed_Ici : IsClosed (Set.Ici (1 : ℝ))).mem_of_mapClusterPt meanCluster
  apply Eventually.of_forall
  intro depth
  change 1 ≤ ∫ marks, chemicalOrbit rule p positive belowOne fixedPoint growth depth marks
    ∂independentInnovationLaw rule p positive belowOne fixedPoint
  rw [chemicalOrbit_mean rule classical p positive belowOne fixedPoint growth growthPositive.le]
  apply (le_div_iff₀ (pow_pos growthPositive depth)).mpr
  simpa only [one_mul] using lowerMeans depth

end IGSIII.Chemical.Substitution
