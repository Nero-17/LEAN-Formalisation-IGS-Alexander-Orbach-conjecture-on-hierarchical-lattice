import IGSIII.Chemical.OrbitLpConvergence
import IGSIII.Chemical.ChemicalOmegaMean

set_option autoImplicit false

namespace IGSIII.Chemical.Substitution

open Universality MeasureTheory Filter IGSIII.Chemical.SmallBall
open scoped ENNReal Topology

theorem chemical_mean_ratio_tendsto_of_l1_convergence
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthNonnegative : 0 ≤ growth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (valueMeanOne : (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = 1)
    (amplitude : ℝ)
    (convergence : Tendsto (fun depth => eLpNorm
      (⇑(chemicalOrbit rule p positive belowOne fixedPoint growth depth) - ⇑(amplitude • value))
      1 (independentInnovationLaw rule p positive belowOne fixedPoint)) atTop (𝓝 0)) :
    Tendsto (fun depth => manuscriptDistanceMean rule p depth / growth ^ depth) atTop (𝓝 amplitude) := by
  have integralConvergence := tendsto_integral_of_L1' (⇑(amplitude • value)) (Lp.aestronglyMeasurable _)
    (Filter.Eventually.of_forall (fun depth => (Lp.memLp
      (chemicalOrbit rule p positive belowOne fixedPoint growth depth)).integrable (by norm_num))) convergence
  have integralLimit : (∫ marks, (amplitude • value) marks
      ∂independentInnovationLaw rule p positive belowOne fixedPoint) = amplitude := by
    rw [integral_congr_ae (Lp.coeFn_smul amplitude value)]
    simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul, valueMeanOne, mul_one]
  simpa only [chemicalOrbit_mean rule classical p positive belowOne fixedPoint growth growthNonnegative,
    integralLimit] using integralConvergence

end IGSIII.Chemical.Substitution
