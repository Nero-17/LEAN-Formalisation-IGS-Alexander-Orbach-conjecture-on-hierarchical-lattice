import IGSIII.Chemical.SmallBall.PairedPathBarrier
import IGSIII.Chemical.ShortestLp
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

namespace IGSIII.Chemical.SmallBall

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

variable {Edge Sample : Type*} [Fintype Edge] [DecidableEq Edge] [MeasurableSpace Sample]

theorem measure_paired_exponential_le (measure : Measure Sample)
    (first second : Sample → ℝ) (parameter scale : ℝ)
    (firstMemLp : MemLp (fun sample => Real.exp (parameter * first sample)) 2 measure)
    (secondMemLp : MemLp (fun sample => Real.exp (-parameter * scale * second sample)) 2 measure) :
    (∫ sample, Real.exp (parameter * (first sample - scale * second sample)) ∂measure) ≤
      Real.sqrt (∫ sample, Real.exp (2 * parameter * first sample) ∂measure) *
        Real.sqrt (∫ sample, Real.exp (-2 * parameter * scale * second sample) ∂measure) := by
  have factor (sample : Sample) :
      Real.exp (parameter * first sample) * Real.exp (-parameter * scale * second sample) =
        Real.exp (parameter * (first sample - scale * second sample)) := by rw [← Real.exp_add]; congr 1 <;> ring
  have firstSquare (sample : Sample) :
      Real.exp (parameter * first sample) ^ (2 : ℝ) = Real.exp (2 * parameter * first sample) := by
    rw [Real.rpow_two, ← Real.exp_nat_mul]
    congr 1 <;> ring
  have secondSquare (sample : Sample) :
      Real.exp (-parameter * scale * second sample) ^ (2 : ℝ) = Real.exp (-2 * parameter * scale * second sample) := by
    rw [Real.rpow_two, ← Real.exp_nat_mul]
    congr 1 <;> ring
  have bound := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := 2) (q := 2) (by norm_num [Real.holderConjugate_iff])
    (Filter.Eventually.of_forall (fun sample => Real.exp_nonneg (parameter * first sample)))
    (Filter.Eventually.of_forall (fun sample => Real.exp_nonneg (-parameter * scale * second sample)))
    (by simpa using firstMemLp) (by simpa using secondMemLp)
  simpa only [factor, firstSquare, secondSquare, ← Real.sqrt_eq_rpow] using bound

theorem measure_product_paired_path_barrier
    (measure : Edge → Measure Sample) [∀ edge, IsProbabilityMeasure (measure edge)]
    (first second : Edge → Sample → ℝ)
    (firstMeasurable : ∀ edge, Measurable (first edge)) (secondMeasurable : ∀ edge, Measurable (second edge))
    (path : Finset Edge) {parameter scale ratio : ℝ} (parameterNonnegative : 0 ≤ parameter)
    (pairedIntegrable : ∀ edge ∈ path,
      Integrable (fun sample => Real.exp (parameter * (first edge sample - scale * second edge sample))) (measure edge))
    (pairedBound : ∀ edge ∈ path,
      (∫ sample, Real.exp (parameter * (first edge sample - scale * second edge sample)) ∂measure edge) ≤ ratio) :
    (Measure.pi measure).real {sample : Edge → Sample |
      scale * PathFamily.pathCost path (fun edge => second edge (sample edge)) <
        PathFamily.pathCost path (fun edge => first edge (sample edge))} ≤ ratio ^ path.card := by
  classical
  let factor (edge : Edge) (sample : Sample) : ℝ :=
    if edge ∈ path then Real.exp (parameter * (first edge sample - scale * second edge sample)) else 1
  have factorIntegrable (edge : Edge) : Integrable (factor edge) (measure edge) := by
    by_cases membership : edge ∈ path
    · simpa only [factor, membership, if_true] using pairedIntegrable edge membership
    · simp only [factor, membership, if_false]
      exact integrable_const 1
  have productIntegrable := Integrable.fintype_prod factorIntegrable
  have exponentialIdentity (sample : Edge → Sample) :
      (∏ edge, factor edge (sample edge)) = Real.exp (parameter *
        (PathFamily.pathCost path (fun edge => first edge (sample edge)) -
          scale * PathFamily.pathCost path (fun edge => second edge (sample edge)))) := by
    simp only [factor, Finset.prod_ite_mem_eq, ← Real.exp_sum]
    congr 1
    simp only [PathFamily.pathCost, mul_sub, Finset.mul_sum, Finset.sum_sub_distrib, mul_assoc]
  have firstCostMeasurable : Measurable (fun sample : Edge → Sample =>
      PathFamily.pathCost path (fun edge => first edge (sample edge))) :=
    Finset.measurable_sum _ (fun edge _ => (firstMeasurable edge).comp (measurable_pi_apply edge))
  have secondCostMeasurable : Measurable (fun sample : Edge → Sample =>
      PathFamily.pathCost path (fun edge => second edge (sample edge))) :=
    Finset.measurable_sum _ (fun edge _ => (secondMeasurable edge).comp (measurable_pi_apply edge))
  have eventMeasurable := measurableSet_lt (secondCostMeasurable.const_mul scale) firstCostMeasurable
  have comparison : (Measure.pi measure).real {sample : Edge → Sample |
      scale * PathFamily.pathCost path (fun edge => second edge (sample edge)) <
        PathFamily.pathCost path (fun edge => first edge (sample edge))} ≤
      ∫ sample, ∏ edge, factor edge (sample edge) ∂Measure.pi measure := by
    have indicatorIntegral := integral_indicator_const (μ := Measure.pi measure) (1 : ℝ) eventMeasurable
    simp only [smul_eq_mul, mul_one] at indicatorIntegral
    rw [← indicatorIntegral]
    apply integral_mono ((integrable_const 1).indicator eventMeasurable) productIntegrable
    intro sample
    dsimp only
    rw [exponentialIdentity]
    simp only [indicator_apply, mem_setOf_eq]
    split_ifs with bad
    · rw [Real.one_le_exp_iff]
      exact mul_nonneg parameterNonnegative (sub_nonneg.mpr bad.le)
    · exact Real.exp_nonneg _
  refine comparison.trans ?_
  rw [integral_fintype_prod_eq_prod]
  have localIntegral (edge : Edge) : (∫ sample, factor edge sample ∂measure edge) =
      if edge ∈ path then (∫ sample, Real.exp (parameter * (first edge sample - scale * second edge sample)) ∂measure edge) else 1 := by
    by_cases membership : edge ∈ path <;> simp [factor, membership]
  simp_rw [localIntegral]
  rw [Finset.prod_ite_mem_eq]
  simpa only [Finset.prod_const] using Finset.prod_le_prod
    (fun edge _ => integral_nonneg (fun sample => Real.exp_nonneg _)) pairedBound

theorem measure_product_shortest_paired_barrier (family : PathFamily Edge)
    (measure : Edge → Measure Sample) [∀ edge, IsProbabilityMeasure (measure edge)]
    (first second : Edge → Sample → ℝ)
    (firstMeasurable : ∀ edge, Measurable (first edge)) (secondMeasurable : ∀ edge, Measurable (second edge))
    {parameter scale ratio : ℝ} (parameterNonnegative : 0 ≤ parameter)
    (pairedIntegrable : ∀ path ∈ family.paths, ∀ edge ∈ path,
      Integrable (fun sample => Real.exp (parameter * (first edge sample - scale * second edge sample))) (measure edge))
    (pairedBound : ∀ path ∈ family.paths, ∀ edge ∈ path,
      (∫ sample, Real.exp (parameter * (first edge sample - scale * second edge sample)) ∂measure edge) ≤ ratio) :
    (Measure.pi measure).real {sample : Edge → Sample |
      scale * family.shortest (fun edge => second edge (sample edge)) <
        family.shortest (fun edge => first edge (sample edge))} ≤
      ∑ path ∈ family.paths, ratio ^ path.card := by
  have subset : {sample : Edge → Sample |
      scale * family.shortest (fun edge => second edge (sample edge)) <
        family.shortest (fun edge => first edge (sample edge))} ⊆
      ⋃ path ∈ family.paths, {sample : Edge → Sample |
        scale * PathFamily.pathCost path (fun edge => second edge (sample edge)) <
          PathFamily.pathCost path (fun edge => first edge (sample edge))} := by
    intro sample bad
    obtain ⟨path, membership, minimizing⟩ := family.exists_minimizer (fun edge => second edge (sample edge))
    refine mem_iUnion.mpr ⟨path, mem_iUnion.mpr ⟨membership, ?_⟩⟩
    rw [mem_setOf_eq, ← minimizing]
    exact bad.trans_le (family.shortest_le_pathCost _ membership)
  exact (measureReal_mono (μ := Measure.pi measure) subset (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le (μ := Measure.pi measure) family.paths _).trans
    (Finset.sum_le_sum (fun path membership => measure_product_paired_path_barrier measure first second
      firstMeasurable secondMeasurable path parameterNonnegative (pairedIntegrable path membership) (pairedBound path membership))))

end
end IGSIII.Chemical.SmallBall
