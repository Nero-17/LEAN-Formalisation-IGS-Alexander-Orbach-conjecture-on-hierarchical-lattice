import IGSIII.Geometry.CellLocalisationMarkedCompletionLaw

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall IGSIII.Probability
open MeasureTheory ProbabilityTheory GromovHausdorff Filter
open scoped Topology ENNReal

/-- The labelled metric code and the genuine measurable completion family
can be chosen from one and the same actual scalar witness. This prevents an
unrelated eigenfield or chemical scale from being inserted into the joint law. -/
theorem exists_actual_critical_marked_completed_cell_family
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ constant growth amplitude : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      ∃ growthGreaterThanOne : 1 < growth,
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧ 1 ≤ amplitude ∧
      (∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
        manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) ∧
      ∃ value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint),
        (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address,
          0 < chemicalField rule p positive belowOne fixedPoint value address marks ∧
          Tendsto (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
            atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks))) ∧
        ∃ family : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Bool → Bool → GHSpace,
          Measurable family ∧
          Measurable (markedChemicalCompletionCode rule p positive belowOne fixedPoint growth amplitude value family) ∧
          ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address opened sourceSide,
            Tendsto (fun depth => markedAddressRootedFiniteGH rule growth (zero_lt_one.trans growthGreaterThanOne)
              depth marks address opened sourceSide) atTop (𝓝 (family (innovationTreeShift rule address marks) opened sourceSide)) := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds, value, _, _, _,
    amplitude, amplitudeAtLeastOne, fieldLimits, _, _, _, _⟩ :=
    exists_actual_chemical_scalar rule classicalRule p positive belowOne fixedPoint
  have growthGreaterThanOne : 1 < growth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le growthLower
  obtain ⟨family, familyMeasurable, rootLimits⟩ := exists_measurable_rooted_completion_family_of_terminal_field
    rule classicalRule p positive belowOne fixedPoint constant growth amplitude growthGreaterThanOne
    (zero_lt_one.trans_le amplitudeAtLeastOne) meanBounds value
    (fieldLimits.mono (fun marks fields address => (fields address).1))
    (fieldLimits.mono (fun marks fields address => (fields address).2.2))
  refine ⟨constant, growth, amplitude, constantPositive, constantAtMostOne, growthGreaterThanOne,
    growthLower, growthUpper, amplitudeAtLeastOne, meanBounds, value,
    fieldLimits.mono (fun marks fields address => ⟨(fields address).1, (fields address).2.2⟩),
    family, familyMeasurable,
    markedChemicalCompletionCode_measurable rule p positive belowOne fixedPoint growth amplitude value family familyMeasurable, ?_⟩
  apply ae_all_iff.mpr
  intro address
  have shiftedLimits := rootLimits
  rw [← (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).map_eq] at shiftedLimits
  have transferred := ae_of_ae_map (innovationTreeShift_measurable rule address).aemeasurable shiftedLimits
  filter_upwards [transferred] with marks limits
  intro opened sourceSide
  exact (limits opened sourceSide).congr' (Eventually.of_forall (fun depth =>
    (markedAddressRootedFiniteGH_shift rule growth (zero_lt_one.trans growthGreaterThanOne) depth marks address opened sourceSide).symm))
end
end IGSIII.Geometry
