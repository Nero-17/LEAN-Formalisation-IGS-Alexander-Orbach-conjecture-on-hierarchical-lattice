import IGSIII.Geometry.ComponentRadiusSupremumMoments
import IGSIII.Geometry.ActualSkeletonNets

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Geometry
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Chemical.SmallBall MeasureTheory Filter
open scoped ENNReal Topology BigOperators

/-- The diameter of one actual planted component. In a noncrossing socket the
source and target components are evaluated separately on their shared marks. -/
def terminalRetainedComponentDiameter {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges) (sourceSide : Bool) : ℕ :=
  Finset.univ.sup (fun pair : Fin vertices × Fin vertices =>
    if (network.openGraph configuration).Reachable (plantedVertex network sourceSide) pair.1 ∧
       (network.openGraph configuration).Reachable (plantedVertex network sourceSide) pair.2 then
      (network.openGraph configuration).dist pair.1 pair.2 else 0)

lemma terminalRetainedComponentDiameter_le_twice_radius {vertices edges : ℕ}
    (network : FiniteNetwork vertices edges) (configuration : Configuration edges) (sourceSide : Bool) :
    terminalRetainedComponentDiameter network configuration sourceSide ≤ 2 * terminalComponentRadius network configuration := by
  classical
  apply Finset.sup_le
  intro pair _
  split_ifs with connected
  · have triangle := connected.1.symm.dist_triangle_left pair.2
    rw [show (network.openGraph configuration).dist pair.1 (plantedVertex network sourceSide) =
      (network.openGraph configuration).dist (plantedVertex network sourceSide) pair.1 from SimpleGraph.dist_comm] at triangle
    have firstBound := planted_distance_le_terminalComponentRadius network configuration sourceSide pair.1
    have lastBound := planted_distance_le_terminalComponentRadius network configuration sourceSide pair.2
    omega
  · exact Nat.zero_le _

def markedRetainedComponentDiameter (rule : Rule) (depth : ℕ)
    (address : List (Fin rule.edges)) (opened sourceSide : Bool)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℕ :=
  terminalRetainedComponentDiameter (rule.generation depth).network
    (markedGenerationConfiguration rule marks depth address opened) sourceSide

def markedComponentDiameterSupremum (rule : Rule) (growth : ℝ)
    (address : List (Fin rule.edges)) (opened sourceSide : Bool)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  ⨆ depth, (markedRetainedComponentDiameter rule depth address opened sourceSide marks : ℝ) / growth ^ (depth + 1)

lemma markedRetainedComponentDiameter_measurable (rule : Rule) (depth : ℕ)
    (address : List (Fin rule.edges)) (opened sourceSide : Bool) :
    Measurable (markedRetainedComponentDiameter rule depth address opened sourceSide) :=
  (measurable_of_finite (fun configuration => terminalRetainedComponentDiameter
    (rule.generation depth).network configuration sourceSide)).comp
      (markedGenerationConfiguration_measurable rule depth address opened)

lemma markedComponentDiameterSupremum_measurable (rule : Rule) (growth : ℝ)
    (address : List (Fin rule.edges)) (opened sourceSide : Bool) :
    Measurable (markedComponentDiameterSupremum rule growth address opened sourceSide) :=
  Measurable.iSup (fun depth => ((measurable_of_countable (fun value : ℕ => (value : ℝ))).comp
    (markedRetainedComponentDiameter_measurable rule depth address opened sourceSide)).div_const _)

/-- The all-depth moment estimate uses exactly the chemical scale of any scalar
witness satisfying the manuscript mean bounds. -/
theorem actual_critical_component_radius_supremum_moments_of_mean_bounds
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) :
    (∀ order : ℝ≥0∞, order ≠ ∞ → ∀ address opened,
      MemLp (markedComponentRadiusSupremum rule growth address opened) order
        (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address opened depth,
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / growth ^ (depth + 1) ≤
        markedComponentRadiusSupremum rule growth address opened marks := by
  obtain ⟨otherConstant, otherGrowth, _, _, growthLower, _, otherBounds, moments, terminalBound⟩ :=
    exists_actual_chemical_terminal_envelope rule classicalRule p positive belowOne fixedPoint
  have otherGrowthPositive : 0 < otherGrowth :=
    (show (0 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast Nat.zero_lt_of_lt classicalRule.scale).trans_le growthLower
  have growthIdentity := IGSIII.Probability.exponential_growth_unique (manuscriptDistanceMean rule p)
    growth otherGrowth constant⁻¹ otherConstant⁻¹ growthPositive otherGrowthPositive meanBounds otherBounds
  subst otherGrowth
  have growthGreaterThanOne : 1 < growth :=
    (show (1 : ℝ) < (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) by
      exact_mod_cast classicalRule.scale).trans_le growthLower
  have properties (order : ℝ≥0∞) (orderFinite : order ≠ ∞) :=
    markedComponentRadiusSupremum_memLp_of_terminal_envelopes rule
      (independentInnovationLaw rule p positive belowOne fixedPoint) growth growthGreaterThanOne
      (chemicalTerminalEnvelope rule p positive belowOne fixedPoint growth)
      (chemicalTerminalEnvelope_measurable rule p positive belowOne fixedPoint growth)
      (fun power powerPositive => by
        obtain ⟨bound, finite, bounds⟩ := moments power (by exact_mod_cast powerPositive) (by simp)
        exact ⟨bound, finite, fun address opened => (bounds address opened).2⟩)
      terminalBound order orderFinite
  exact ⟨fun order finite => (properties order finite).1, (properties 2 (by norm_num)).2⟩

/-- Appendix full-mesh, moment assertion, on the actual common innovation tree.
This treats each B side as its own intrinsic component without changing marks. -/
theorem actual_critical_component_diameter_supremum_moments_of_mean_bounds
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (constant growth : ℝ) (growthPositive : 0 < growth)
    (meanBounds : ∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
      manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) :
    (∀ order : ℝ≥0∞, order ≠ ∞ → ∀ address opened sourceSide,
      MemLp (markedComponentDiameterSupremum rule growth address opened sourceSide) order
        (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address opened sourceSide depth,
      (markedRetainedComponentDiameter rule depth address opened sourceSide marks : ℝ) / growth ^ (depth + 1) ≤
        markedComponentDiameterSupremum rule growth address opened sourceSide marks := by
  obtain ⟨radiusMoments, radiusBounds⟩ := actual_critical_component_radius_supremum_moments_of_mean_bounds
    rule classicalRule p positive belowOne fixedPoint constant growth growthPositive meanBounds
  have properties (order : ℝ≥0∞) (orderFinite : order ≠ ∞)
      (address : List (Fin rule.edges)) (opened sourceSide : Bool) :=
    IGSIII.Probability.supremum_memLp_of_lp_dominator
      (independentInnovationLaw rule p positive belowOne fixedPoint) order
      (fun depth marks => (markedRetainedComponentDiameter rule depth address opened sourceSide marks : ℝ) / growth ^ (depth + 1))
      (fun depth => ((measurable_of_countable (fun value : ℕ => (value : ℝ))).comp
        (markedRetainedComponentDiameter_measurable rule depth address opened sourceSide)).div_const _)
      (Eventually.of_forall (fun marks depth => div_nonneg (Nat.cast_nonneg _) (pow_nonneg growthPositive.le _)))
      ((radiusMoments order orderFinite address opened).const_mul 2).toLp
      (by
        filter_upwards [radiusBounds, MemLp.coeFn_toLp ((radiusMoments order orderFinite address opened).const_mul 2)]
          with marks bounds identity
        rw [identity]
        intro depth
        have diameterBound := terminalRetainedComponentDiameter_le_twice_radius (rule.generation depth).network
          (markedGenerationConfiguration rule marks depth address opened) sourceSide
        have castBound : (markedRetainedComponentDiameter rule depth address opened sourceSide marks : ℝ) ≤
            2 * (markedTerminalComponentRadius rule marks depth address opened : ℝ) := by exact_mod_cast diameterBound
        calc
          _ ≤ (2 * (markedTerminalComponentRadius rule marks depth address opened : ℝ)) / growth ^ (depth + 1) :=
            div_le_div_of_nonneg_right castBound (pow_pos growthPositive _).le
          _ = 2 * ((markedTerminalComponentRadius rule marks depth address opened : ℝ) / growth ^ (depth + 1)) := by ring
          _ ≤ 2 * markedComponentRadiusSupremum rule growth address opened marks :=
            mul_le_mul_of_nonneg_left (bounds address opened depth) (by norm_num))
  refine ⟨fun order finite address opened sourceSide => (properties order finite address opened sourceSide).1, ?_⟩
  exact ae_all_iff.mpr (fun address => ae_all_iff.mpr (fun opened => ae_all_iff.mpr
    (fun sourceSide => (properties 2 (by norm_num) address opened sourceSide).2)))

end
end IGSIII.Geometry

