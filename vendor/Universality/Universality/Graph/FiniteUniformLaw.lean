import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.Independence.InfinitePi

namespace Universality
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β : Type*} [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
variable [MeasurableSpace α] [MeasurableSpace β]
variable [MeasurableSingletonClass α] [MeasurableSingletonClass β]

theorem finiteUniform_equiv_measurePreserving (equivalence : α ≃ β) :
    MeasurePreserving equivalence (PMF.uniformOfFintype α).toMeasure
      (PMF.uniformOfFintype β).toMeasure := by
  refine ⟨measurable_of_countable _, ?_⟩
  apply Measure.ext_of_singleton
  intro vertex
  rw [Measure.map_apply (measurable_of_countable equivalence) (measurableSet_singleton vertex)]
  have heq : equivalence ⁻¹' {vertex} = {equivalence.symm vertex} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact equivalence.apply_eq_iff_eq_symm_apply
  rw [heq]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_congr equivalence]

theorem finiteUniform_prod :
    (PMF.uniformOfFintype α).toMeasure.prod (PMF.uniformOfFintype β).toMeasure =
      (PMF.uniformOfFintype (α × β)).toMeasure := by
  apply Measure.ext_of_singleton
  rintro ⟨first, second⟩
  conv_lhs => rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul]
  exact (ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top (Fintype.card β)))
    (Or.inl (ENNReal.natCast_ne_top (Fintype.card α)))).symm

theorem finiteUniform_pi (n : ℕ) :
    Measure.pi (fun _ : Fin n => (PMF.uniformOfFintype α).toMeasure) =
      (PMF.uniformOfFintype (Fin n → α)).toMeasure := by
  apply Measure.ext_of_singleton
  intro word
  rw [Measure.pi_singleton]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, Fintype.card_fun, Fintype.card_fin,
    Finset.prod_const, Finset.card_univ, Nat.cast_pow, ENNReal.inv_pow]

/-- An iid uniform ancestral sequence has exactly the uniform law on each
finite prefix, derived from the full infinite product law. -/
theorem finiteUniform_prefix_measurePreserving (n : ℕ) :
    MeasurePreserving (fun word : ℕ → α => fun i : Fin n => word i.val)
      (Measure.infinitePi (fun _ : ℕ => (PMF.uniformOfFintype α).toMeasure))
      (PMF.uniformOfFintype (Fin n → α)).toMeasure := by
  refine ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply i.val), ?_⟩
  rw [Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective,
    Measure.infinitePi_eq_pi, finiteUniform_pi]

end
end Universality
