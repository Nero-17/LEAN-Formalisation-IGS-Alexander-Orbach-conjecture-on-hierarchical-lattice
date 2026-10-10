import IGSIII.Chemical.OrbitSupremumMoments
import IGSIII.Probability.DominatedLpConvergence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace IGSIII.Chemical.Substitution

open Universality MeasureTheory Filter IGSIII.Probability IGSIII.Chemical.SmallBall
open scoped ENNReal Topology

theorem chemicalOrbit_all_finite_lp_of_ae_tendsto
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valueFixed : normalizedChemicalTransferLp rule p positive belowOne fixedPoint 2 growth value = value)
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, 0 < value marks)
    (lower upper : ℝ) (lowerPositive : 0 < lower) (upperPositive : 0 < upper)
    (comparison : ∀ member ∈ chemicalOmegaSet rule p positive belowOne fixedPoint growth,
      lower • value ≤ member ∧ member ≤ upper • value)
    (limit : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (convergence : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      Tendsto (fun depth => chemicalOrbit rule p positive belowOne fixedPoint growth depth marks) atTop (𝓝 (limit marks)))
    (order : ℝ≥0∞) (orderPositive : order ≠ 0) (orderFinite : order ≠ ∞) :
    MemLp limit order (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
    (∀ depth, MemLp (chemicalOrbit rule p positive belowOne fixedPoint growth depth)
      order (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
    Tendsto (fun depth => eLpNorm
      (⇑(chemicalOrbit rule p positive belowOne fixedPoint growth depth) - ⇑limit)
      order (independentInnovationLaw rule p positive belowOne fixedPoint)) atTop (𝓝 0) := by
  letI : Fact (1 ≤ max 1 order) := ⟨le_max_left _ _⟩
  have largerOrderFinite : max (1 : ℝ≥0∞) order ≠ ∞ :=
    (max_lt (by norm_num : (1 : ℝ≥0∞) < ∞) orderFinite.lt_top).ne
  have supremum := chemicalOrbit_supremum_memLp_of_endogenous_field rule classical p positive belowOne fixedPoint
    constant growth constantPositive growthPositive meanBounds value valueFixed valuePositive
    lower upper lowerPositive upperPositive comparison (max 1 order) largerOrderFinite
  have supremumMemLp := supremum.1.mono_exponent (le_max_right (1 : ℝ≥0∞) order)
  have nonnegative := chemicalOrbit_ae_deterministic_bounds rule p positive belowOne fixedPoint growth growthPositive
  have bounds : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      0 ≤ limit marks ∧ limit marks ≤
        ⨆ depth, chemicalOrbit rule p positive belowOne fixedPoint growth depth marks := by
    filter_upwards [convergence, supremum.2, nonnegative] with marks sampleConvergence sampleBounds sampleNonnegative
    exact ⟨ge_of_tendsto' sampleConvergence (fun depth => (sampleNonnegative depth).1),
      le_of_tendsto' sampleConvergence sampleBounds⟩
  have limitMemLp : MemLp limit order (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    apply supremumMemLp.mono' (Lp.aestronglyMeasurable limit)
    filter_upwards [bounds] with marks sampleBounds
    rw [Real.norm_eq_abs, abs_of_nonneg sampleBounds.1]
    exact sampleBounds.2
  have sequenceMemLp (depth : ℕ) : MemLp (chemicalOrbit rule p positive belowOne fixedPoint growth depth)
      order (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    apply supremumMemLp.mono' (Lp.aestronglyMeasurable _)
    filter_upwards [supremum.2, nonnegative] with marks sampleBounds sampleNonnegative
    rw [Real.norm_eq_abs, abs_of_nonneg (sampleNonnegative depth).1]
    exact sampleBounds depth
  refine ⟨limitMemLp, sequenceMemLp, ?_⟩
  apply eLpNorm_tendsto_zero_of_dominated_ae _ order orderPositive orderFinite _ limit _
    (fun depth => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable limit) supremumMemLp _ convergence
  intro depth
  filter_upwards [bounds, supremum.2, nonnegative] with marks limitBounds sequenceBounds sequenceNonnegative
  have supremumNonnegative := (sequenceNonnegative 0).1.trans (sequenceBounds 0)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg supremumNonnegative]
  apply abs_le.mpr
  constructor <;> linarith [sequenceBounds depth, (sequenceNonnegative depth).1]

end IGSIII.Chemical.Substitution
