import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace Universality
noncomputable section
open MeasureTheory

variable {sample : ℕ → Type*} [∀ age, MeasurableSpace (sample age)]

theorem measurable_ageSampleEmbedding (age : ℕ) :
    Measurable (Sigma.mk age : sample age → Σ age, sample age) :=
  Measurable.of_le_map (iInf_le _ age)

theorem measurableSet_ageSample_iff (event : Set (Σ age, sample age)) :
    MeasurableSet event ↔ ∀ age, MeasurableSet (Sigma.mk age ⁻¹' event) :=
  MeasurableSpace.measurableSet_iInf

/-- A countable mixture on a genuine disjoint union of sample spaces. -/
def countableAgeMixture (ageLaw : Measure ℕ) (law : ∀ age, Measure (sample age)) :
    Measure (Σ age, sample age) :=
  Measure.sum (fun age => ageLaw {age} • (law age).map (Sigma.mk age))

theorem countableAgeMixture_apply (ageLaw : Measure ℕ)
    (law : ∀ age, Measure (sample age)) {event : Set (Σ age, sample age)}
    (hmeasurable : MeasurableSet event) :
    countableAgeMixture ageLaw law event =
      ∑' age, ageLaw {age} * law age (Sigma.mk age ⁻¹' event) := by
  unfold countableAgeMixture
  rw [Measure.sum_apply _ hmeasurable]
  apply tsum_congr
  intro age
  rw [Measure.smul_apply, Measure.map_apply (measurable_ageSampleEmbedding age) hmeasurable]
  rfl

instance countableAgeMixture_probability (ageLaw : Measure ℕ) [IsProbabilityMeasure ageLaw]
    (law : ∀ age, Measure (sample age)) [∀ age, IsProbabilityMeasure (law age)] :
    IsProbabilityMeasure (countableAgeMixture ageLaw law) := by
  constructor
  rw [countableAgeMixture_apply ageLaw law MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ, mul_one]
  have hsum := measure_iUnion (μ := ageLaw) (f := fun age : ℕ => ({age} : Set ℕ))
    (by simp [Pairwise]) (fun age => measurableSet_singleton age)
  have hcover : (⋃ age : ℕ, ({age} : Set ℕ)) = Set.univ := by
    ext age
    simp
  rw [hcover, measure_univ] at hsum
  exact hsum.symm

theorem countableAgeMixture_real_apply (ageLaw : Measure ℕ) [IsProbabilityMeasure ageLaw]
    (law : ∀ age, Measure (sample age)) [∀ age, IsProbabilityMeasure (law age)]
    {event : Set (Σ age, sample age)} (hmeasurable : MeasurableSet event) :
    (countableAgeMixture ageLaw law).real event =
      ∑' age, ageLaw.real {age} * (law age).real (Sigma.mk age ⁻¹' event) := by
  rw [measureReal_def, countableAgeMixture_apply ageLaw law hmeasurable,
    ENNReal.tsum_toReal_eq (fun age =>
      ENNReal.mul_ne_top (measure_ne_top ageLaw _) (measure_ne_top (law age) _))]
  apply tsum_congr
  intro age
  exact ENNReal.toReal_mul

end
end Universality
