import Universality.Geometry.GenerationHausdorffDimension
import Universality.Section5.CertificateConsequences

/-!
The ambient Section 5 growth formula is the Hausdorff dimension of the actual
compact completion of rescaled generation graph metrics. The finite allocation
certificates remain explicit hypotheses in the generic construction statements.
-/

namespace Universality.Section5
noncomputable section

theorem RuleResponses.hausdorff_dimension {rule : Rule} {base : ℕ}
    (responses : RuleResponses rule base) (base_gt_one : 1 < base) :
    dimH (Set.univ : Set (Rule.GenerationMetricSpace responses.classical)) =
      ENNReal.ofReal (58 / 25) := by
  rw [Rule.generationMetricSpace_dimH_eq responses.classical,
    (responses.dimensions base_gt_one).1]

theorem ExactAllocationCertificate.hausdorff_dimension {depth base offset : ℕ}
    {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth base offset allocation) :
    dimH (Set.univ : Set (Rule.GenerationMetricSpace certificate.classical)) =
      ENNReal.ofReal (Real.log ((base : ℝ) ^ 232) /
        Real.log (base ^ 100 + offset : ℕ)) := by
  rw [Rule.generationMetricSpace_dimH_eq certificate.classical,
    certificate.logarithmic_dimensions.1]

theorem ExactAllocationCertificate.shifted_hausdorff_dimension {depth : ℕ}
    {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth 19 480 allocation) :
    dimH (Set.univ : Set (Rule.GenerationMetricSpace certificate.classical)) =
      ENNReal.ofReal (232 * (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ))) := by
  rw [Rule.generationMetricSpace_dimH_eq certificate.classical,
    certificate.shifted_dimensions.1]

theorem ExactAllocationCertificate.shifted_hausdorff_dimension_toReal {depth : ℕ}
    {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth 19 480 allocation) :
    (dimH (Set.univ : Set (Rule.GenerationMetricSpace certificate.classical))).toReal =
      232 * (Real.log 19 / Real.log ((19 : ℕ) ^ 100 + 480 : ℕ)) := by
  rw [certificate.shifted_hausdorff_dimension, ENNReal.toReal_ofReal]
  exact mul_nonneg (by norm_num) (div_nonneg (Real.log_nonneg (by norm_num))
    (Real.log_nonneg (by exact_mod_cast shifted_scale_gt_one.le)))

/-- The accepted Gelfond--Schneider interface is used only for transcendence. -/
theorem ExactAllocationCertificate.shifted_hausdorff_dimension_transcendental {depth : ℕ}
    {allocation : List Bool → ℕ}
    (certificate : ExactAllocationCertificate depth 19 480 allocation) :
    Transcendental ℚ
      (dimH (Set.univ : Set (Rule.GenerationMetricSpace certificate.classical))).toReal := by
  rw [certificate.shifted_hausdorff_dimension_toReal]
  have transcendence := certificate.shifted_dimensions_transcendental.1
  rw [certificate.shifted_dimensions.1] at transcendence
  exact transcendence

end
end Universality.Section5
