import IGSIII34.Spectral.ActualCylinderMassCompletion20261011
import IGSIII34.Spectral.PositiveComponentCountCompletion20261011
import IGSIII34.Spectral.PerronTypicalMassCompletion20261011

/-! Typical mass on the actual nested component boundary. Its weights are
the limits of the actual retained vertex ratios. Both exponential bounds
hold on the same boundary law and the same innovation environment. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped Topology ENNReal BigOperators

theorem exists_actual_typical_component_mass_completion20261011
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ weight : List (Fin rule.edges × Bool) →
        (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        weight [] marks = 1 ∧
        (∀ address, 0 ≤ weight address marks ∧
          weight address marks = ∑ choice : Fin rule.edges × Bool, weight (address ++ [choice]) marks ∧
          Tendsto (fun depth => markedOrientedVertexMass rule marks depth (componentEdgeAddress address)
            (retainedComponentState rule marks address) /
              markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
            atTop (𝓝 (weight address marks))) ∧
        ∃ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
          IsProbabilityMeasure boundary ∧
          (∀ depth word, boundary {path | path depth = word} =
            ENNReal.ofReal (weight (List.ofFn word) marks)) ∧
          ∀ᵐ path ∂boundary,
            (∀ depth, Fin.init (path (depth + 1)) = path depth ∧
              0 < weight (List.ofFn (path depth)) marks) ∧
            ∀ growth : ℝ, 1 < growth → ∃ bound : ℝ, 0 < bound ∧ ∃ threshold : ℕ,
              ∀ depth, threshold ≤ depth →
                (growth ^ depth)⁻¹ < weight (List.ofFn (path depth)) marks *
                  ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth ∧
                weight (List.ofFn (path depth)) marks *
                  ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth ≤
                    bound * growth ^ depth := by
  classical
  obtain ⟨weight, properties⟩ := exists_actual_component_weight_subexponential_upper classicalRule
    p positive belowOne fixedPoint
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  refine ⟨weight, ?_⟩
  filter_upwards [properties,
    actual_positive_component_weight_Perron_count_bound_completion20261011 rule classicalRule
      p positive belowOne fixedPoint] with marks properties counts
  have nonnegative : ∀ address, 0 ≤ weight address marks := fun address => (properties.2.1 address).1
  have compatible : ∀ address, weight address marks =
      ∑ choice : Fin rule.edges × Bool, weight (address ++ [choice]) marks :=
    fun address => (properties.2.1 address).2.1
  have inactiveZero : ∀ address, retainedComponentState rule marks address = .inactive → weight address marks = 0 :=
    fun address => (properties.2.1 address).2.2.2.1
  obtain ⟨coefficient, coefficientPositive, counts⟩ := counts
  have countBound := counts (fun address => weight address marks) inactiveZero
  obtain ⟨_, fallbackEdge, _⟩ := rule.network.exists_pivotal_configuration (classicalRule.connected _)
  let boundary := cylinderBoundaryLaw (fallbackEdge, true) (fun address => weight address marks)
    nonnegative properties.1 compatible
  have atoms : ∀ depth word, boundary {path | path depth = word} =
      ENNReal.ofReal (weight (List.ofFn word) marks) :=
    cylinderBoundaryLaw_atom (fallbackEdge, true) (fun address => weight address marks)
      nonnegative properties.1 compatible
  have rationalLower : ∀ ratio : ℚ, ∀ᵐ path ∂boundary,
      0 ≤ (ratio : ℝ) → (ratio : ℝ) < 1 → ∀ᶠ depth in atTop,
        0 < weight (List.ofFn (path depth)) marks →
          (ratio : ℝ) ^ depth < weight (List.ofFn (path depth)) marks *
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth := by
    intro ratio
    by_cases nonnegativeRatio : 0 ≤ (ratio : ℝ)
    · by_cases below : (ratio : ℝ) < 1
      · exact (ae_partition_Perron_mass_eventually_lower boundary
          (fun depth => Fin depth → (Fin rule.edges × Bool)) (fun depth path => path depth)
          (fun _ word => weight (List.ofFn word) marks) atoms _ coefficient radiusPositive
          coefficientPositive.le countBound (ratio : ℝ) nonnegativeRatio below).mono
            (fun _ property _ _ => property)
      · exact Filter.Eventually.of_forall (fun _ _ impossible => (below impossible).elim)
    · exact Filter.Eventually.of_forall (fun _ impossible _ => (nonnegativeRatio impossible).elim)
  refine ⟨properties.1, (fun address => ⟨(properties.2.1 address).1,
    (properties.2.1 address).2.1, (properties.2.1 address).2.2.1⟩),
    boundary, cylinderBoundaryLaw_probability _ _ _ _ _, atoms, ?_⟩
  filter_upwards [ae_all_iff.mpr rationalLower,
    cylinderBoundaryLaw_positive_prefixes (fallbackEdge, true) (fun address => weight address marks)
      nonnegative properties.1 compatible,
    cylinderBoundaryLaw_extends (fallbackEdge, true) (fun address => weight address marks)
      nonnegative properties.1 compatible] with path lower positivePrefixes nested
  refine ⟨fun depth => ⟨nested depth, positivePrefixes depth⟩, ?_⟩
  intro growth greater
  obtain ⟨ratio, aboveInverse, belowOneRatio⟩ := exists_rat_btwn (inv_lt_one_of_one_lt₀ greater)
  have ratioNonnegative : 0 ≤ (ratio : ℝ) :=
    (inv_pos.mpr (zero_lt_one.trans greater)).le.trans aboveInverse.le
  obtain ⟨lowerThreshold, lowerEstimates⟩ := eventually_atTop.mp
    (lower ratio ratioNonnegative belowOneRatio)
  obtain ⟨bound, boundPositive, upperThreshold, upperEstimates⟩ := properties.2.2 growth greater
  refine ⟨bound, boundPositive, max lowerThreshold upperThreshold, ?_⟩
  intro depth after
  constructor
  · have comparison : (growth ^ depth)⁻¹ ≤ (ratio : ℝ) ^ depth := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (inv_pos.mpr (zero_lt_one.trans greater)).le aboveInverse.le _
    exact comparison.trans_lt
      (lowerEstimates depth ((le_max_left _ _).trans after) (positivePrefixes depth))
  · simpa only [List.length_ofFn] using upperEstimates (List.ofFn (path depth))
      (by simpa using ((le_max_right lowerThreshold upperThreshold).trans after))

end
end IGSIII34.Spectral
