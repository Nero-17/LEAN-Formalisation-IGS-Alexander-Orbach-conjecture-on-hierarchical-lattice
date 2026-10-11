import Universality.Probability.IndependentSumLaw
import Mathlib.MeasureTheory.Measure.Support

namespace Universality
noncomputable section
open MeasureTheory
open scoped Topology ENNReal

theorem continuous_map_support {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (measure : Measure X) (f : X → Y) (hf : Continuous f) (point : X)
    (hpoint : point ∈ measure.support) : f point ∈ (measure.map f).support := by
  rw [Measure.support_eq_forall_isOpen] at hpoint ⊢
  intro neighborhood hmem hopen
  rw [Measure.map_apply hf.measurable hopen.measurableSet]
  exact hpoint _ hmem (hopen.preimage hf)

theorem independent_product_support {index : Type*} [Fintype index]
    (law : index → Measure ℝ) [∀ i, IsProbabilityMeasure (law i)]
    (point : index → ℝ) (hpoint : ∀ i, point i ∈ (law i).support) :
    point ∈ (Measure.pi law).support := by
  rw [Measure.support_eq_forall_isOpen]
  intro neighborhood hmem hopen
  obtain ⟨coordinate, hcoordinate, hsubset⟩ := isOpen_pi_iff'.mp hopen point hmem
  have hpositive : 0 < (Measure.pi law) (Set.univ.pi coordinate) := by
    rw [Measure.pi_pi]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact ((Measure.mem_support_iff_forall _).mp (hpoint i) _
      ((hcoordinate i).1.mem_nhds (hcoordinate i).2)).ne'
  exact hpositive.trans_le (measure_mono hsubset)

theorem independent_sum_support {index : Type*} [Fintype index]
    (law : index → Measure ℝ) [∀ i, IsProbabilityMeasure (law i)]
    (point : index → ℝ) (hpoint : ∀ i, point i ∈ (law i).support) :
    (∑ i, point i) ∈ (independentSumLaw law).support :=
  continuous_map_support (Measure.pi law) (fun value => ∑ i, value i) (by fun_prop) point
    (independent_product_support law point hpoint)

theorem finite_mixture_support {index : Type*} [Fintype index]
    (weight : index → ℝ) (law : index → Measure ℝ)
    (chosen : index) (hweight : 0 < weight chosen) (point : ℝ)
    (hpoint : point ∈ (law chosen).support) :
    point ∈ (finiteMixtureLaw weight law).support := by
  classical
  rw [Measure.support_eq_forall_isOpen] at hpoint ⊢
  intro neighborhood hmem hopen
  have hpositive : 0 < ENNReal.ofReal (weight chosen) * law chosen neighborhood :=
    ENNReal.mul_pos_iff.mpr ⟨ENNReal.ofReal_pos.mpr hweight, hpoint _ hmem hopen⟩
  apply hpositive.trans_le
  simp only [finiteMixtureLaw, Measure.coe_finset_sum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul]
  exact Finset.single_le_sum (f := fun i => ENNReal.ofReal (weight i) * law i neighborhood)
    (fun i _ => bot_le) (Finset.mem_univ chosen)

theorem exists_positive_support_of_positive_mean (measure : Measure ℝ)
    (hmean : 0 < ∫ x, x ∂measure) : ∃ point : ℝ, 0 < point ∧ point ∈ measure.support := by
  by_contra hnot
  have hnonpositive : ∀ point ∈ measure.support, point ≤ 0 := by
    intro point hpoint
    by_contra hp
    exact hnot ⟨point, lt_of_not_ge hp, hpoint⟩
  have hsupport : ∀ᵐ x ∂measure, x ∈ measure.support := measure.support_mem_ae
  have hmeanNonpos : (∫ x, x ∂measure) ≤ 0 :=
    integral_nonpos_of_ae (hsupport.mono (fun x hx => hnonpositive x hx))
  exact (not_le_of_gt hmean) hmeanNonpos

end
end Universality
