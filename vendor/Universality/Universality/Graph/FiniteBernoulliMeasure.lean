import Universality.Percolation.Bernoulli
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Tactic.Ring

namespace Universality
noncomputable section
attribute [local instance] Classical.propDecidable
open MeasureTheory ProbabilityTheory

theorem finiteMeasure_real_event_eq_sum {α : Type*} [Fintype α]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    (law : Measure α) [IsFiniteMeasure law] (event : α → Prop) :
    law.real {value | event value} =
      ∑ value, if event value then law.real {value} else 0 := by
  have heq : {value | event value} =
      (↑(Finset.univ.filter event) : Set α) := by ext value; simp
  rw [heq, ← sum_measureReal_singleton]
  simp only [Finset.sum_filter]

theorem finiteUniform_real_singleton {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (value : α) :
    (PMF.uniformOfFintype α).toMeasure.real {value} = 1 / (Fintype.card α : ℝ) := by
  simp only [measureReal_def, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]

variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

theorem bernoulliMeasure_real_singleton (p : unitInterval) (opened : Bool) :
    (bernoulliMeasure true false p).real {opened} =
      if opened then (p : ℝ) else 1 - p := by
  cases opened <;> simp [bernoulliMeasure_real_apply]

/-- The genuine finite product measure has the same atoms as the pre-existing
finite weighted-sum definition of percolation. -/
theorem finiteBernoulli_real_singleton (edges : ℕ) (p : unitInterval)
    (configuration : FiniteNetwork.Configuration edges) :
    (Measure.pi (fun _ : Fin edges => bernoulliMeasure true false p)).real {configuration} =
      FiniteNetwork.bernoulliWeight (p : ℝ) configuration := by
  rw [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro edge hedge
  exact bernoulliMeasure_real_singleton p (configuration edge)

theorem finiteUniformBernoulli_event {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (edges : ℕ) (p : unitInterval)
    (event : α → FiniteNetwork.Configuration edges → Prop) :
    ((PMF.uniformOfFintype α).toMeasure.prod
      (Measure.pi (fun _ : Fin edges => bernoulliMeasure true false p))).real
        {input | event input.1 input.2} =
      (∑ configuration, FiniteNetwork.bernoulliWeight (p : ℝ) configuration *
        ∑ value, if event value configuration then (1 : ℝ) else 0) / Fintype.card α := by
  rw [finiteMeasure_real_event_eq_sum]
  have hatom (value : α) (configuration : FiniteNetwork.Configuration edges) :
      ((PMF.uniformOfFintype α).toMeasure.prod
        (Measure.pi (fun _ : Fin edges => bernoulliMeasure true false p))).real
          {(value, configuration)} =
        (1 / (Fintype.card α : ℝ)) * FiniteNetwork.bernoulliWeight (p : ℝ) configuration := by
    rw [← Set.singleton_prod_singleton, measureReal_prod_prod,
      finiteUniform_real_singleton, finiteBernoulli_real_singleton]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hatom]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro configuration hconfiguration
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro value hvalue
  split_ifs <;> ring

theorem mappedFiniteUniformBernoulli_event {α β : Type*}
    [Fintype α] [Nonempty α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] (root : α → β) (hroot : Measurable root)
    (edges : ℕ) (p : unitInterval) (event : β → FiniteNetwork.Configuration edges → Prop)
    (hevent : MeasurableSet {input : β × FiniteNetwork.Configuration edges |
      event input.1 input.2}) :
    (((PMF.uniformOfFintype α).toMeasure.map root).prod
      (Measure.pi (fun _ : Fin edges => bernoulliMeasure true false p))).real
        {input | event input.1 input.2} =
      (∑ configuration, FiniteNetwork.bernoulliWeight (p : ℝ) configuration *
        ∑ value, if event (root value) configuration then (1 : ℝ) else 0) / Fintype.card α := by
  have hmap := (hroot.measurePreserving (PMF.uniformOfFintype α).toMeasure).prod
    (MeasurePreserving.id (Measure.pi (fun _ : Fin edges => bernoulliMeasure true false p)))
  rw [measureReal_def, ← hmap.map_eq, Measure.map_apply hmap.measurable hevent]
  exact finiteUniformBernoulli_event edges p (fun value configuration => event (root value) configuration)

end
end Universality
