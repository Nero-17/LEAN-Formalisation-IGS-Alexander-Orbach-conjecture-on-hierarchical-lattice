import IGSIII.Geometry.CellLocalisationGH
import IGSIII.Geometry.GenericComponentLengths

set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open MeasureTheory ProbabilityTheory GromovHausdorff Filter IGSIII.Chemical.SmallBall
open scoped Topology ENNReal

/-- The joint C/N and source/target family is a measurable random compact
metric space, obtained as the limit of the actual microscopic planted clusters. -/
theorem exists_measurable_rooted_completion_family_of_terminal_field
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth amplitude : ℝ) (growthGreaterThanOne : 1 < growth) (amplitudePositive : 0 < amplitude)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth)
    (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (fieldPositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 < chemicalField rule p positive belowOne fixedPoint value address marks)
    (fieldConvergence : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth => (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1))
        atTop (𝓝 (amplitude * chemicalField rule p positive belowOne fixedPoint value address marks))) :
    ∃ family : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → Bool → Bool → GHSpace,
      Measurable family ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ opened sourceSide,
        Tendsto (fun depth => markedRootedFiniteGH rule growth (lt_trans zero_lt_one growthGreaterThanOne) depth marks opened sourceSide)
          atTop (𝓝 (family marks opened sourceSide)) := by
  have growthPositive : 0 < growth := lt_trans zero_lt_one growthGreaterThanOne
  let eta : ℝ := (growth + 1) / (2 * growth)
  have etaPositive : 0 < eta := div_pos (by linarith) (by positivity)
  have etaBelowOne : eta < 1 := (div_lt_one (by positivity : 0 < 2 * growth)).mpr (by linarith)
  have productGreaterThanOne : 1 < growth * eta := by
    have identity : growth * eta = (growth + 1) / 2 := by dsimp [eta]; field_simp
    rw [identity]
    linarith
  have coefficientNonnegative : 0 ≤ (rule.edges + 1 : ℝ) / (1 - eta) :=
    div_nonneg (by positivity) (sub_pos.mpr etaBelowOne).le
  have converges (opened sourceSide : Bool) :
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∃ limiting : GHSpace, Tendsto (fun depth => markedRootedFiniteGH rule growth growthPositive depth marks opened sourceSide)
          atTop (𝓝 limiting) := by
    filter_upwards [fieldPositive, fieldConvergence,
      independentInnovationLaw_crosses rule p positive belowOne fixedPoint,
      marked_generations_coherent_ae rule p positive belowOne fixedPoint,
      actual_critical_component_mesh_of_mean_bounds rule classicalRule p positive belowOne fixedPoint constant growth growthPositive
        meanBounds eta etaPositive etaBelowOne productGreaterThanOne] with marks fieldsPositive fieldsConvergence crossing coherent mesh
    obtain ⟨start, radiusBounds⟩ := mesh
    obtain ⟨lengthNonnegative, lengthPositive, childConvergence⟩ := address_block_lengths_of_terminal_field
      rule p positive belowOne fixedPoint growth amplitude growthPositive amplitudePositive value marks crossing fieldsPositive fieldsConvergence [] opened 0
    letI := rootedComponentSpace_compact_of_component_radius_bounds rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] opened) (coherent [] opened) sourceSide growth growthPositive
      marks [] opened (fun _ => rfl)
      (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks [] opened 0)
      lengthNonnegative lengthPositive childConvergence eta ((rule.edges + 1 : ℝ) / (1 - eta)) start
      etaPositive.le etaBelowOne coefficientNonnegative radiusBounds
    refine ⟨toGHSpace (RootedComponentSpace rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] opened) (coherent [] opened) sourceSide growth growthPositive 0
      (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks [] opened 0)
      lengthNonnegative lengthPositive childConvergence), ?_⟩
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact rootedFiniteComponent_ghDist_tendsto_zero_of_component_radius_bounds rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] opened) (coherent [] opened) sourceSide growth growthPositive
      marks [] opened (fun _ => rfl)
      (chemicalAddressBlockLimitLength rule p positive belowOne fixedPoint growth amplitude value marks [] opened 0)
      lengthNonnegative lengthPositive childConvergence eta ((rule.edges + 1 : ℝ) / (1 - eta)) start
      etaPositive.le etaBelowOne coefficientNonnegative radiusBounds
  have measurableLimits (opened sourceSide : Bool) := measurable_limit_of_tendsto_metrizable_ae
    (fun depth => (((measurable_pi_apply sourceSide).comp (measurable_pi_apply opened)).comp
      (markedRootedFiniteGH_measurable rule growth growthPositive depth)).aemeasurable) (converges opened sourceSide)
  choose family measurableFamily convergentFamily using measurableLimits
  refine ⟨fun marks opened sourceSide => family opened sourceSide marks,
    measurable_pi_lambda _ (fun opened => measurable_pi_lambda _ (fun sourceSide => measurableFamily opened sourceSide)), ?_⟩
  apply ae_all_iff.mpr
  intro opened
  apply ae_all_iff.mpr
  intro sourceSide
  exact convergentFamily opened sourceSide

/-- A measurable GH limit represents the actual intrinsic completion, by
uniqueness of the limit of its true microscopic component sequence. -/
theorem markedRootedCompletionGH_eq_of_tendsto
    (rule : Rule) (classicalRule : rule.Classical)
    (configuration : ∀ depth, Configuration (rule.generation depth).edges)
    (coherent : configurationSequenceCoherent rule configuration) (sourceSide : Bool)
    (scale : ℝ) (scalePositive : 0 < scale)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) (opened : Bool)
    (configurationIdentity : ∀ depth, configuration depth = markedGenerationConfiguration rule marks depth [] opened)
    (values : ∀ coarse, Fin (rule.generation coarse).edges → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ values depth edge)
    (positive : ∀ depth edge, configuration depth edge = true → 0 < values depth edge)
    (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
      (((rule.generation fine).network.openGraph
        (generationBlockCells rule coarse fine (configuration (coarse + fine + 1)) edge)).dist
          (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
        scale ^ (coarse + fine + 2 + 0)) atTop (𝓝 (values coarse edge)))
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ descendant state depth, start ≤ descendant.length →
      (markedTerminalComponentRadius rule marks depth descendant state : ℝ) /
        scale ^ (depth + 1 + descendant.length) ≤ coefficient * eta ^ descendant.length)
    (limiting : GHSpace)
    (convergence : Tendsto (fun depth => markedRootedFiniteGH rule scale scalePositive depth marks opened sourceSide) atTop (𝓝 limiting)) :
    letI := rootedComponentSpace_compact_of_component_radius_bounds rule classicalRule configuration coherent sourceSide scale scalePositive
      marks [] opened configurationIdentity values nonnegative positive childConvergence eta coefficient start etaNonnegative etaBelowOne
      coefficientNonnegative radiusBounds
    limiting = toGHSpace (RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive 0
      values nonnegative positive childConvergence) := by
  letI := rootedComponentSpace_compact_of_component_radius_bounds rule classicalRule configuration coherent sourceSide scale scalePositive
    marks [] opened configurationIdentity values nonnegative positive childConvergence eta coefficient start etaNonnegative etaBelowOne
    coefficientNonnegative radiusBounds
  have actualConvergence := rootedFiniteComponent_ghDist_tendsto_zero_of_component_radius_bounds rule classicalRule configuration coherent sourceSide scale scalePositive
    marks [] opened configurationIdentity values nonnegative positive childConvergence eta coefficient start etaNonnegative etaBelowOne
    coefficientNonnegative radiusBounds
  have actualLimit : Tendsto (fun depth => toGHSpace (RootedFiniteComponent rule configuration sourceSide scale scalePositive 0 depth)) atTop
      (𝓝 (toGHSpace (RootedComponentSpace rule classicalRule configuration coherent sourceSide scale scalePositive 0
        values nonnegative positive childConvergence))) := tendsto_iff_dist_tendsto_zero.mpr actualConvergence
  apply tendsto_nhds_unique convergence
  apply actualLimit.congr'
  exact Eventually.of_forall (fun depth => rootedFiniteComponentGH_configuration_congr rule configuration
    (fun age => markedGenerationConfiguration rule marks age [] opened) sourceSide scale scalePositive 0 depth (configurationIdentity depth))
end
end IGSIII.Geometry

