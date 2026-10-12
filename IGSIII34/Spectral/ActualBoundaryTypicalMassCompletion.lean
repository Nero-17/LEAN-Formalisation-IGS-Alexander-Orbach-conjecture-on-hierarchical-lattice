import IGSIII34.Spectral.PositiveComponentCountCompletion
import IGSIII34.Spectral.PerronTypicalMassCompletion
import IGSIII.Mass.CylinderCounts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Mass
open MeasureTheory Filter Matrix
open scoped Topology BigOperators

theorem finite_partition_positive_weight_ae_completion
    {Point Index : Type*} [MeasurableSpace Point] [Fintype Index]
    (measure : Measure Point) (index : Point → Index) (weight : Index → ℝ)
    (atoms : ∀ label, measure {point | index point = label} = ENNReal.ofReal (weight label)) :
    ∀ᵐ point ∂measure, 0 < weight (index point) := by
  have each (label : Index) : ∀ᵐ point ∂measure, index point = label → 0 < weight label := by
    by_cases positive : 0 < weight label
    · exact Eventually.of_forall (fun _ _ => positive)
    · have zero := atoms label
      rw [ENNReal.ofReal_of_nonpos (le_of_not_gt positive)] at zero
      apply ae_iff.mpr
      simpa only [positive, imp_false, not_not] using zero
  filter_upwards [ae_all_iff.mpr each] with point positive
  exact positive (index point) rfl

/-- The typical Perron lower mass estimate applies to any version of the
actual vertex-ratio weights and any boundary law with their genuine atoms.
It does not choose an unrelated mass measure. -/
theorem actual_boundary_vertex_ratio_typical_lower_completion
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (weight : List (Fin rule.edges × Bool) → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks))) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)),
      (∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks)) →
      ∀ᵐ path ∂boundary, (∀ depth, 0 < weight (List.ofFn (path depth)) marks) ∧
        ∀ slack : ℝ, 1 < slack → ∀ᶠ depth in atTop,
          (slack^depth)⁻¹ < weight (List.ofFn (path depth)) marks *
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^depth := by
  classical
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  filter_upwards [actualRatios, actual_positive_component_weight_Perron_count_bound_completion
    rule classicalRule p positive belowOne fixedPoint] with marks ratios counts
  have inactiveZero : ∀ address, retainedComponentState rule marks address = .inactive → weight address marks = 0 := by
    intro address inactive
    have zeroLimit : Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected) atTop (𝓝 (0 : ℝ)) := by
      simpa only [inactive, markedOrientedVertexMass_inactive, zero_div] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    exact tendsto_nhds_unique (ratios address) zeroLimit
  obtain ⟨coefficient, coefficientPositive, counts⟩ := counts
  have countBound := counts (fun address => weight address marks) inactiveZero
  intro boundary atoms
  have positivePrefixes : ∀ᵐ path ∂boundary, ∀ depth, 0 < weight (List.ofFn (path depth)) marks := by
    apply ae_all_iff.mpr
    intro depth
    exact finite_partition_positive_weight_ae_completion boundary (fun path => path depth)
      (fun word => weight (List.ofFn word) marks) (atoms depth)
  have rational (ratio : ℚ) : ∀ᵐ path ∂boundary, 0 ≤ (ratio : ℝ) → (ratio : ℝ) < 1 →
      ∀ᶠ depth in atTop, 0 < weight (List.ofFn (path depth)) marks →
        (ratio : ℝ)^depth < weight (List.ofFn (path depth)) marks *
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^depth := by
    by_cases nonnegative : 0 ≤ (ratio : ℝ)
    · by_cases below : (ratio : ℝ) < 1
      · exact (ae_partition_Perron_mass_eventually_lower boundary
          (fun depth => Fin depth → (Fin rule.edges × Bool)) (fun depth path => path depth)
          (fun _ word => weight (List.ofFn word) marks) atoms _ coefficient radiusPositive coefficientPositive.le
          countBound (ratio : ℝ) nonnegative below).mono (fun _ property _ _ => property)
      · exact Eventually.of_forall (fun _ _ impossible => (below impossible).elim)
    · exact Eventually.of_forall (fun _ impossible _ => (nonnegative impossible).elim)
  filter_upwards [positivePrefixes, ae_all_iff.mpr rational] with path positivePrefixes estimates
  refine ⟨positivePrefixes, ?_⟩
  intro slack greater
  obtain ⟨ratio, inverseBelow, belowOneRatio⟩ := exists_rat_btwn (inv_lt_one_of_one_lt₀ greater)
  have nonnegativeRatio : 0 ≤ (ratio : ℝ) := (inv_pos.mpr (zero_lt_one.trans greater)).le.trans inverseBelow.le
  filter_upwards [estimates ratio nonnegativeRatio belowOneRatio] with depth estimate
  have lowerComparison : (slack^depth)⁻¹ ≤ (ratio : ℝ)^depth := by
    rw [← inv_pow]
    exact pow_le_pow_left₀ (inv_pos.mpr (zero_lt_one.trans greater)).le inverseBelow.le _
  exact lowerComparison.trans_lt (estimate (positivePrefixes depth))

end
end IGSIII34.Spectral
