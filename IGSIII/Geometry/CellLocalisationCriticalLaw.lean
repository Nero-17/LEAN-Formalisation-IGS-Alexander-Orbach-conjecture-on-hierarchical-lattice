import IGSIII.Geometry.CellLocalisationGHLimit
import IGSIII.Geometry.CellLocalisationCompletionLaw
import IGSIII.Geometry.CellLocalisationAddressScaling

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability IGSIII.Chemical.SmallBall
open MeasureTheory ProbabilityTheory GromovHausdorff Filter
open scoped Topology ENNReal

def markedAddressRootedFiniteGH (rule : Rule) (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges)) (opened sourceSide : Bool) : GHSpace :=
  toGHSpace (RootedFiniteComponent rule (fun age => markedGenerationConfiguration rule marks age address opened)
    sourceSide scale scalePositive 0 depth)

theorem markedAddressRootedFiniteGH_shift (rule : Rule) (scale : ℝ) (scalePositive : 0 < scale) (depth : ℕ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (address : List (Fin rule.edges)) (opened sourceSide : Bool) :
    markedAddressRootedFiniteGH rule scale scalePositive depth marks address opened sourceSide =
      markedRootedFiniteGH rule scale scalePositive depth (innovationTreeShift rule address marks) opened sourceSide := by
  exact rootedFiniteComponentGH_configuration_congr rule _ _ sourceSide scale scalePositive 0 depth
    (by simpa only [List.append_nil] using (markedGenerationConfiguration_shift rule marks address depth [] opened).symm)

/-- At the actual critical parameter there is a measurable joint family of
completed C/N planted spaces. Every actual descendant, normalized in its own
root units, is the corresponding shifted member of this family. -/
theorem exists_actual_critical_completed_cell_family
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p) :
    ∃ growth : ℝ, ∃ growthGreaterThanOne : 1 < growth,
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      ∃ family : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Bool → Bool → GHSpace,
        Measurable family ∧
        ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address opened sourceSide,
          Tendsto (fun depth => markedAddressRootedFiniteGH rule growth (lt_trans zero_lt_one growthGreaterThanOne)
            depth marks address opened sourceSide) atTop (𝓝 (family (innovationTreeShift rule address marks) opened sourceSide)) := by
  obtain ⟨constant, growth, _, _, growthLower, growthUpper, meanBounds, value, _, _, _,
    amplitude, amplitudeAtLeastOne, fieldLimits, _, _, _, _⟩ :=
    exists_actual_chemical_scalar rule classicalRule p positive belowOne fixedPoint
  have growthGreaterThanOne : 1 < growth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le growthLower
  obtain ⟨family, familyMeasurable, rootLimits⟩ := exists_measurable_rooted_completion_family_of_terminal_field
    rule classicalRule p positive belowOne fixedPoint constant growth amplitude growthGreaterThanOne
    (lt_of_lt_of_le zero_lt_one amplitudeAtLeastOne) meanBounds value
    (fieldLimits.mono (fun marks fields address => (fields address).1))
    (fieldLimits.mono (fun marks fields address => (fields address).2.2))
  refine ⟨growth, growthGreaterThanOne, growthLower, growthUpper, family, familyMeasurable, ?_⟩
  apply ae_all_iff.mpr
  intro address
  have shiftedLimits := rootLimits
  rw [← (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).map_eq] at shiftedLimits
  have transferred := ae_of_ae_map (innovationTreeShift_measurable rule address).aemeasurable shiftedLimits
  filter_upwards [transferred] with marks limits
  intro opened sourceSide
  exact (limits opened sourceSide).congr' (Eventually.of_forall (fun depth =>
    (markedAddressRootedFiniteGH_shift rule growth (lt_trans zero_lt_one growthGreaterThanOne) depth marks address opened sourceSide).symm))

end
end IGSIII.Geometry
