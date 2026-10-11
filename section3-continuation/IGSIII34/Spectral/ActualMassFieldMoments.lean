import IGSIII34.Spectral.OrientedMassMoments
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! One actual joint mass field on the original innovation tree, with all
positive integer moments uniformly over addresses and oriented states. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped Topology ENNReal

theorem actual_oriented_history_limit_aestronglyMeasurable
    {rule : Rule} (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (parent : OrientedState) (growth : ℝ)
    (limit : (Π depth, rule.ConfigurationHistory depth) → ℝ)
    (convergence : ∀ᵐ path ∂Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint parent.massOpened,
      Tendsto (fun depth => ((rule.generation depth).network.internalStateMass parent
        (Rule.ConfigurationHistory.latest rule depth (path depth)) : ℝ) / growth ^ depth)
        atTop (𝓝 (limit path))) :
    AEStronglyMeasurable limit (Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint parent.massOpened) := by
  apply aestronglyMeasurable_of_tendsto_ae atTop _ convergence
  intro depth
  exact ((measurable_of_countable (fun history : rule.ConfigurationHistory depth =>
    ((rule.generation depth).network.internalStateMass parent
      (Rule.ConfigurationHistory.latest rule depth history) : ℝ) / growth ^ depth)).comp
    (measurable_pi_apply depth)).aestronglyMeasurable

theorem exists_actual_mass_field_all_nat_moments
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ limit : List (Fin rule.edges) → OrientedState →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      (∀ address marks, limit address .inactive marks = 0) ∧
      (∀ address marks, limit address .both marks =
        limit address .sourceOnly marks + limit address .targetOnly marks) ∧
      (∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address parent,
        0 ≤ limit address parent marks ∧
        Tendsto (fun depth => markedOrientedVertexMass rule marks depth address parent /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ depth)
          atTop (𝓝 (limit address parent marks)) ∧
        (parent = .connected → 0 < limit address parent marks)) ∧
      (∀ address parent, AEStronglyMeasurable (limit address parent)
        (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
      ∀ power : ℕ, ∃ bound : ℝ, 0 < bound ∧ ∀ address parent,
        (∫⁻ marks, ENNReal.ofReal (limit address parent marks) ^ power
          ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ ENNReal.ofReal bound := by
  obtain ⟨rootLimit, inactive, split, convergence⟩ := classicalRule.oriented_mask_vertex_limits
    p positive belowOne fixedPoint
  have rootMeasurable (parent : OrientedState) : AEStronglyMeasurable (rootLimit parent)
      (Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint parent.massOpened) :=
    actual_oriented_history_limit_aestronglyMeasurable p positive belowOne fixedPoint parent _
      (rootLimit parent) ((convergence parent).mono (fun _ converges => converges.2.1))
  refine ⟨(fun address parent marks => rootLimit parent (markedHistoryPath rule address parent.massOpened marks)),
    (fun address marks => inactive _), (fun address marks => split _), ?_, ?_, ?_⟩
  · apply ae_all_iff.mpr
    intro address
    apply ae_all_iff.mpr
    intro parent
    have marginal := convergence parent
    rw [← independentInnovationLaw_history_path rule p positive belowOne fixedPoint address parent.massOpened] at marginal
    have pulled := ae_of_ae_map (markedHistoryPath_measurable rule address parent.massOpened).aemeasurable marginal
    filter_upwards [pulled] with marks converges
    simpa only [markedOrientedVertexMass, markedHistoryPath, Rule.ConfigurationHistory.latest_ofFine] using converges
  · intro address parent
    have measurable := rootMeasurable parent
    rw [← independentInnovationLaw_history_path rule p positive belowOne fixedPoint address parent.massOpened] at measurable
    exact measurable.comp_aemeasurable (markedHistoryPath_measurable rule address parent.massOpened).aemeasurable
  · intro power
    obtain ⟨bound, boundPositive, momentBounds⟩ := actual_oriented_history_limit_uniform_nat_moment
      classicalRule p positive belowOne fixedPoint power
    refine ⟨bound, boundPositive, ?_⟩
    intro address parent
    have integrandMeasurable : AEMeasurable (fun path => ENNReal.ofReal (rootLimit parent path) ^ power)
        (Rule.ConfigurationHistory.infiniteLaw rule p positive belowOne fixedPoint parent.massOpened) :=
      (ENNReal.continuous_ofReal.measurable.comp_aemeasurable (rootMeasurable parent).aemeasurable).pow_const power
    have historyLaw := independentInnovationLaw_history_path rule p positive belowOne fixedPoint address parent.massOpened
    have mappedMeasurable : AEMeasurable (fun path => ENNReal.ofReal (rootLimit parent path) ^ power)
        ((independentInnovationLaw rule p positive belowOne fixedPoint).map
          (markedHistoryPath rule address parent.massOpened)) := by
      rwa [historyLaw]
    have equality := lintegral_map' mappedMeasurable
      (markedHistoryPath_measurable rule address parent.massOpened).aemeasurable
    rw [historyLaw] at equality
    rw [← equality]
    exact momentBounds parent (rootLimit parent) ((convergence parent).mono (fun _ converges => converges.2.1))

end
end IGSIII34.Spectral
