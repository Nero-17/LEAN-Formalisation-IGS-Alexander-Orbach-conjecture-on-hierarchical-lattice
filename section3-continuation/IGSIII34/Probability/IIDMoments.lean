import IGSIII34.Probability.MomentInterpolation
import Mathlib.Probability.Independence.Integration
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

theorem iid_lintegral_product_powers {Edge : Type*} [Fintype Edge]
    (law : ProbabilityMeasure ℝ≥0) (powers : Edge → ℕ) :
    (∫⁻ input : Edge → ℝ≥0, ∏ edge, (input edge : ℝ≥0∞) ^ powers edge
      ∂Measure.pi (fun _ : Edge => (law : Measure ℝ≥0))) =
      ∏ edge, ∫⁻ value, (value : ℝ≥0∞) ^ powers edge ∂(law : Measure ℝ≥0) := by
  have independent : iIndepFun
      (fun edge (input : Edge → ℝ≥0) => (input edge : ℝ≥0∞) ^ powers edge)
      (Measure.pi (fun _ : Edge => (law : Measure ℝ≥0))) :=
    iIndepFun_pi (fun edge => (measurable_id.coe_nnreal_ennreal.pow_const (powers edge)).aemeasurable)
  rw [lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ independent
    (fun edge => (measurable_pi_apply edge).coe_nnreal_ennreal.pow_const (powers edge))]
  apply Finset.prod_congr rfl
  intro edge _
  exact (measurePreserving_eval (fun _ : Edge => (law : Measure ℝ≥0)) edge).lintegral_comp
    (measurable_id.coe_nnreal_ennreal.pow_const (powers edge))

theorem iid_lintegral_sum_power {Edge : Type*} [Fintype Edge] [DecidableEq Edge]
    (law : ProbabilityMeasure ℝ≥0) (power : ℕ) :
    (∫⁻ input : Edge → ℝ≥0, (∑ edge, (input edge : ℝ≥0∞)) ^ power
      ∂Measure.pi (fun _ : Edge => (law : Measure ℝ≥0))) =
      ∑ assignment : Fin power → Edge, ∏ edge,
        ∫⁻ value, (value : ℝ≥0∞) ^ Fintype.card {factor : Fin power // assignment factor = edge}
          ∂(law : Measure ℝ≥0) := by
  classical
  simp_rw [Fintype.sum_pow]
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro assignment _
    have productIdentity (input : Edge → ℝ≥0) :
        (∏ factor, (input (assignment factor) : ℝ≥0∞)) =
          ∏ edge, (input edge : ℝ≥0∞) ^ Fintype.card {factor : Fin power // assignment factor = edge} := by
      rw [← Fintype.prod_fiberwise' assignment (fun edge => (input edge : ℝ≥0∞))]
      simp only [Finset.prod_const, Finset.card_univ]
    simp_rw [productIdentity]
    exact iid_lintegral_product_powers law _
  · intro assignment _
    exact Finset.univ.measurable_prod
      (fun factor _ => (measurable_pi_apply (assignment factor)).coe_nnreal_ennreal)

end
end IGSIII34.Probability
