import IGSIII34.Percolation.BernoulliThinning
import IGSIII34.Percolation.LawMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal

theorem iid_finite_marking_lintegral {Index Outcome Mark : Type*}
    [Fintype Index] [DecidableEq Index] [MeasurableSpace Outcome] [Fintype Mark]
    [MeasurableSpace Mark] [MeasurableSingletonClass Mark]
    (law : ProbabilityMeasure Outcome) (mark : Outcome → Mark) (markMeasurable : Measurable mark)
    (response : (Index → Mark) → ℝ≥0∞) :
    (∫⁻ input : Index → Outcome, response (fun index => mark (input index))
      ∂Measure.pi (fun _ : Index => (law : Measure Outcome))) =
        ∑ marking : Index → Mark, response marking *
          ∏ index, (law : Measure Outcome) {value | mark value = marking index} := by
  have jointMeasurable : Measurable (fun input : Index → Outcome => fun index => mark (input index)) :=
    measurable_pi_lambda _ (fun index => markMeasurable.comp (measurable_pi_apply index))
  rw [← lintegral_map (f := response) (measurable_of_finite response) jointMeasurable,
    Measure.pi_map_pi (fun _ => markMeasurable.aemeasurable), lintegral_fintype]
  apply Finset.sum_congr rfl
  intro marking _
  rw [Measure.pi_singleton]
  congr 1
  apply Finset.prod_congr rfl
  intro index _
  rw [Measure.map_apply markMeasurable (measurableSet_singleton _)]
  rfl

theorem bool_marking_weights {Outcome : Type*} [MeasurableSpace Outcome]
    (law : ProbabilityMeasure Outcome) (mark : Outcome → Bool) (markMeasurable : Measurable mark)
    (bit : Bool) :
    (law : Measure Outcome) {value | mark value = bit} =
      ENNReal.ofReal (if bit then ((law : Measure Outcome) {value | mark value = true}).toReal
        else 1 - ((law : Measure Outcome) {value | mark value = true}).toReal) := by
  have finite : (law : Measure Outcome) {value | mark value = true} ≠ ∞ := measure_ne_top _ _
  cases bit
  · have complement : {value | mark value = false} = {value | mark value = true}ᶜ := by
      ext value
      cases mark value <;> simp
    have eventMeasurable : MeasurableSet {value | mark value = true} :=
      markMeasurable (measurableSet_singleton _)
    rw [complement, measure_compl (s := {value | mark value = true}) eventMeasurable finite,
      measure_univ]
    simp only [Bool.false_eq_true, ↓reduceIte, ENNReal.ofReal_sub _ ENNReal.toReal_nonneg,
      ENNReal.ofReal_one, ENNReal.ofReal_toReal finite]
  · exact (ENNReal.ofReal_toReal finite).symm

theorem bool_marking_probability_bounds {Outcome : Type*} [MeasurableSpace Outcome]
    (law : ProbabilityMeasure Outcome) (mark : Outcome → Bool) :
    0 ≤ ((law : Measure Outcome) {value | mark value = true}).toReal ∧
      ((law : Measure Outcome) {value | mark value = true}).toReal ≤ 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · have bound : (law : Measure Outcome) {value | mark value = true} ≤ 1 :=
      (measure_mono (Set.subset_univ _)).trans_eq (measure_univ : (law : Measure Outcome) Set.univ = 1)
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top bound

theorem iid_bool_marking_lintegral {edges : ℕ} {Outcome : Type*} [MeasurableSpace Outcome]
    (law : ProbabilityMeasure Outcome) (mark : Outcome → Bool) (markMeasurable : Measurable mark)
    (response : Universality.FiniteNetwork.Configuration edges → ℝ)
    (responseNonnegative : ∀ marking, 0 ≤ response marking) :
    (∫⁻ input : Fin edges → Outcome,
      ENNReal.ofReal (response (fun edge => mark (input edge)))
      ∂Measure.pi (fun _ : Fin edges => (law : Measure Outcome))) =
        ENNReal.ofReal (∑ marking, Universality.FiniteNetwork.bernoulliWeight
          (((law : Measure Outcome) {value | mark value = true}).toReal) marking * response marking) := by
  open Universality.FiniteNetwork in
    have bounds := bool_marking_probability_bounds law mark
    rw [iid_finite_marking_lintegral (Index := Fin edges) law mark markMeasurable
        (fun marking => ENNReal.ofReal (response marking)),
      ENNReal.ofReal_sum_of_nonneg (fun marking _ => mul_nonneg
        (bernoulliWeight_nonneg bounds.1 bounds.2 marking) (responseNonnegative marking))]
    apply Finset.sum_congr rfl
    intro marking _
    rw [ENNReal.ofReal_mul (bernoulliWeight_nonneg bounds.1 bounds.2 marking), mul_comm]
    congr 1
    calc
      _ = ∏ edge, ENNReal.ofReal (if marking edge then
          ((law : Measure Outcome) {value | mark value = true}).toReal else
          1 - ((law : Measure Outcome) {value | mark value = true}).toReal) :=
        Finset.prod_congr rfl (fun edge _ => bool_marking_weights law mark markMeasurable (marking edge))
      _ = _ := (ENNReal.ofReal_prod_of_nonneg (fun edge _ => by
        split_ifs <;> linarith [bounds.1, bounds.2])).symm

end
end IGSIII34.Probability
