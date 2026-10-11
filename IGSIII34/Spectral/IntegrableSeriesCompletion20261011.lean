import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Filter
open scoped ENNReal

theorem integrable_tsum_of_summable_integral_norm_completion20261011
    {Space Index : Type*} [MeasurableSpace Space] [Countable Index]
    (measure : Measure Space) (functions : Index → Space → ℝ)
    (integrable : ∀ index, Integrable (functions index) measure)
    (summable : Summable (fun index => ∫ point, ‖functions index point‖ ∂measure)) :
    Integrable (fun point => ∑' index, functions index point) measure := by
  let lifted : Index → Lp ℝ 1 measure := fun index => (integrable index).toL1 (functions index)
  have norms : ∀ index, ‖lifted index‖ = ∫ point, ‖functions index point‖ ∂measure := by
    intro index
    rw [L1.norm_eq_integral_norm]
    exact integral_congr_ae ((integrable index).coeFn_toL1.fun_comp norm)
  have summableNorms : Summable (fun index => ‖lifted index‖) := by
    simpa only [norms] using summable
  have finiteEnorm : ∑' index, ‖lifted index‖ₑ ≠ ∞ :=
    tsum_enorm_ne_top_iff_summable_norm.mpr summableNorms
  have representatives : ∀ᵐ point ∂measure, ∀ index, lifted index point = functions index point :=
    ae_all_iff.mpr (fun index => (integrable index).coeFn_toL1)
  have equality : (fun point => (∑' index, lifted index : Lp ℝ 1 measure) point) =ᵐ[measure]
      (fun point => ∑' index, functions index point) := by
    filter_upwards [Lp.coeFn_tsum finiteEnorm, representatives] with point sumEquality termEquality
    exact sumEquality.trans (tsum_congr termEquality)
  exact (L1.integrable_coeFn (∑' index, lifted index)).congr equality

end
end IGSIII34.Spectral
