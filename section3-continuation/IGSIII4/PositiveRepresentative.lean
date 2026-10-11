import IGSIII4.SupersolutionInverseMoments
import IGSIII4.TransferAlgebra

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII34.Percolation
open scoped NNReal

theorem exists_positive_nnreal_representative {Sample : Type*} [MeasurableSpace Sample]
    (measure : Measure Sample) (value : Sample → ℝ) (measurable : Measurable value)
    (positive : ∀ᵐ sample ∂measure, 0 < value sample) :
    ∃ representative : Sample → ℝ≥0, Measurable representative ∧
      (∀ sample, 0 < (representative sample : ℝ)) ∧
      (fun sample => (representative sample : ℝ)) =ᵐ[measure] value := by
  refine ⟨fun sample => if 0 < value sample then Real.toNNReal (value sample) else 1,
    Measurable.ite (measurableSet_lt measurable_const measurable)
      (measurable_real_toNNReal.comp measurable) measurable_const, ?_, ?_⟩
  · intro sample
    dsimp only
    split_ifs with above
    · rw [Real.coe_toNNReal _ above.le]
      exact above
    · exact zero_lt_one
  · filter_upwards [positive] with sample above
    simp only [above, if_pos, Real.coe_toNNReal _ above.le]

theorem supersolution_positive_representative (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (measurable : Measurable value)
    (integrable : Integrable value (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint, 0 ≤ value marks)
    (meanPositive : 0 < ∫ marks, value marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint)
    {factor : ℝ} (factorPositive : 0 < factor)
    (supersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule value marks ≤ factor * value marks) :
    ∃ representative : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ≥0,
      Measurable representative ∧ (∀ marks, 0 < (representative marks : ℝ)) ∧
      (fun marks => (representative marks : ℝ)) =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint] value ∧
      Integrable (fun marks => (representative marks : ℝ))
        (independentInnovationLaw rule probability positive belowOne fixedPoint) ∧
      Integrable (fun marks => (representative marks : ℝ)⁻¹)
        (independentInnovationLaw rule probability positive belowOne fixedPoint) ∧
      (0 < ∫ marks, (representative marks : ℝ)⁻¹
        ∂independentInnovationLaw rule probability positive belowOne fixedPoint) ∧
      (∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
        electricalTransfer rule (fun marks => (representative marks : ℝ)) marks ≤
          factor * (representative marks : ℝ)) := by
  have truncatedSame : (fun marks => (Real.toNNReal (value marks) : ℝ))
      =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint] value := by
    filter_upwards [nonnegative] with marks above
    exact Real.coe_toNNReal _ above
  have truncatedMeasurable := measurable_real_toNNReal.comp measurable
  have truncatedIntegrable := integrable.congr truncatedSame.symm
  have truncatedMeanPositive : 0 < ∫ marks, (Real.toNNReal (value marks) : ℝ)
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint := by
    rw [integral_congr_ae truncatedSame]
    exact meanPositive
  have truncatedSupersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      (electricalTransferNNReal rule (fun marks => Real.toNNReal (value marks)) marks : ℝ) ≤
        factor * (Real.toNNReal (value marks) : ℝ) := by
    have transferSame := electricalTransfer_congr_ae rule probability positive belowOne fixedPoint truncatedSame
    filter_upwards [transferSame, truncatedSame, supersolution] with marks transferIdentity identity bound
    change electricalTransfer rule (fun marks => (Real.toNNReal (value marks) : ℝ)) marks ≤ _
    rw [transferIdentity, identity]
    exact bound
  obtain ⟨truncatedPositive, inverseMoments⟩ := supersolution_positive_and_inverse_moments rule classicalRule
    probability positive belowOne fixedPoint (fun marks => Real.toNNReal (value marks))
    truncatedMeasurable truncatedIntegrable truncatedMeanPositive factorPositive truncatedSupersolution
  have valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint, 0 < value marks := by
    filter_upwards [truncatedPositive, truncatedSame] with marks above identity
    rwa [identity] at above
  obtain ⟨representative, representativeMeasurable, representativePositive, same⟩ :=
    exists_positive_nnreal_representative (independentInnovationLaw rule probability positive belowOne fixedPoint)
      value measurable valuePositive
  have representativeIntegrable := integrable.congr same.symm
  have representativeInverseIntegrable : Integrable (fun marks => (representative marks : ℝ)⁻¹)
      (independentInnovationLaw rule probability positive belowOne fixedPoint) := by
    have truncatedInverse : Integrable (fun marks => (Real.toNNReal (value marks) : ℝ)⁻¹)
        (independentInnovationLaw rule probability positive belowOne fixedPoint) := by
      simpa only [pow_one] using inverseMoments 1
    apply truncatedInverse.congr
    filter_upwards [truncatedSame, same] with marks truncatedIdentity identity
    rw [truncatedIdentity, identity]
  have inverseMeanPositive : 0 < ∫ marks, (representative marks : ℝ)⁻¹
      ∂independentInnovationLaw rule probability positive belowOne fixedPoint := by
    apply (integral_pos_iff_support_of_nonneg
      (fun marks => (inv_pos.mpr (representativePositive marks)).le) representativeInverseIntegrable).mpr
    have supportFull : Function.support (fun marks => (representative marks : ℝ)⁻¹) = Set.univ := by
      ext marks
      simp only [Function.mem_support, Set.mem_univ, iff_true]
      exact (inv_pos.mpr (representativePositive marks)).ne'
    rw [supportFull]
    simp
  refine ⟨representative, representativeMeasurable, representativePositive, same,
    representativeIntegrable, representativeInverseIntegrable, inverseMeanPositive, ?_⟩
  have transferSame := electricalTransfer_congr_ae rule probability positive belowOne fixedPoint same
  filter_upwards [transferSame, same, supersolution] with marks transferIdentity identity bound
  rw [transferIdentity, identity]
  exact bound

end
end IGSIII4
