import IGSIII.Chemical.SubstitutionPaths.ActualPrefixVarianceRate20261011

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory
open IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped ENNReal

noncomputable section

theorem rawInnovationPrefixSigma_mono20261011 (rule : Rule)
    {small large : ℕ} (depthBound : small ≤ large) :
    rawInnovationPrefixSigma20261011 rule small ≤
      rawInnovationPrefixSigma20261011 rule large := by
  have restrictionMeasurable : Measurable
      (fun prefixValues :
        ({coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < large} →
          Configuration rule.edges) =>
        fun coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < small} =>
          prefixValues ⟨coordinate.val, lt_of_lt_of_le coordinate.property depthBound⟩) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  exact (restrictionMeasurable.comp
    (comap_measurable (rawInnovationPrefix20261011 rule large))).comap_le

theorem markedObservableLp_rawPrefix_measurable_of_le20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (depth prefixDepth : ℕ)
    (depthBound : depth + 1 ≤ prefixDepth)
    (response : Configuration (rule.generation depth).edges → ℝ) :
    AEStronglyMeasurable[rawInnovationPrefixSigma20261011 rule prefixDepth]
      (markedObservableLp rule p positive belowOne fixedPoint depth [] true response)
      (independentInnovationLaw rule p positive belowOne fixedPoint) :=
  AEStronglyMeasurable.mono (rawInnovationPrefixSigma_mono20261011 rule depthBound)
    (markedObservableLp_rawPrefix_measurable20261011 rule p positive belowOne fixedPoint depth response)

theorem chemicalOrbit_rawPrefix_measurable_of_le20261011
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth) (depth prefixDepth : ℕ)
    (depthBound : depth ≤ prefixDepth) :
    AEStronglyMeasurable[rawInnovationPrefixSigma20261011 rule prefixDepth]
      (chemicalOrbit rule p positive belowOne fixedPoint growth depth)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  cases depth with
  | zero =>
    change AEStronglyMeasurable[rawInnovationPrefixSigma20261011 rule prefixDepth]
      (chemicalUnitLp rule p positive belowOne fixedPoint 2)
      (independentInnovationLaw rule p positive belowOne fixedPoint)
    exact aestronglyMeasurable_const.congr
      (chemicalUnitLp_ae rule p positive belowOne fixedPoint 2).symm
  | succ depth =>
    rw [chemicalOrbit_tail_eq_actual rule classical p positive belowOne fixedPoint growth growthNonnegative]
    exact markedObservableLp_rawPrefix_measurable_of_le20261011 rule p positive belowOne fixedPoint
      depth prefixDepth depthBound (growthScaledDistance rule growth depth)

theorem chemicalOrbit_rawPrefixResidual_zero_of_le20261011
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth) (depth prefixDepth : ℕ)
    (depthBound : depth ≤ prefixDepth) :
    rawPrefixResidual20261011 rule p positive belowOne fixedPoint prefixDepth
      (chemicalOrbit rule p positive belowOne fixedPoint growth depth) = 0 :=
  rawPrefixResidual_zero_of_measurable20261011 rule p positive belowOne fixedPoint prefixDepth _
    (chemicalOrbit_rawPrefix_measurable_of_le20261011 rule classical p positive belowOne fixedPoint
      growth growthNonnegative depth prefixDepth depthBound)

theorem chemicalOrbit_rawPrefixResidual_zero_of_lt20261011
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (growth : ℝ) (growthNonnegative : 0 ≤ growth) (depth prefixDepth : ℕ)
    (depthBound : depth < prefixDepth) :
    rawPrefixResidual20261011 rule p positive belowOne fixedPoint prefixDepth
      (chemicalOrbit rule p positive belowOne fixedPoint growth depth) = 0 :=
  chemicalOrbit_rawPrefixResidual_zero_of_le20261011 rule classical p positive belowOne fixedPoint
    growth growthNonnegative depth prefixDepth depthBound.le

end
end IGSIII.Chemical.Substitution
