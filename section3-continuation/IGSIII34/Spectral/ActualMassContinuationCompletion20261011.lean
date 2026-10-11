import IGSIII34.Spectral.ActualMassFieldMoments
import IGSIII.Probability.IndependentPrefix
import IGSIII.Geometry.CellLocalisationAddressScaling
import IGSIII34.Probability.IndependentConditioning

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

namespace IGSIII34.Spectral
noncomputable section

open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators Topology ENNReal

/-- A measurable, pointwise nonnegative version of the actual mass continuation
on one common innovation tree. Its B sides retain their original coupling. -/
structure ActualMassContinuationCompletion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) where
  mass : OrientedState → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
  measurable : ∀ parent, Measurable (mass parent)
  nonnegative : ∀ parent marks, 0 ≤ mass parent marks
  meanBound : ℝ
  meanBoundPositive : 0 < meanBound
  integrable : ∀ parent, Integrable (mass parent) (independentInnovationLaw rule p positive belowOne fixedPoint)
  means : ∀ parent, (∫ marks, mass parent marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ meanBound
  actualLimits : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
    ∀ address parent,
      Tendsto (fun depth => markedOrientedVertexMass rule marks depth address parent /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^depth)
        atTop (𝓝 (mass parent (innovationTreeShift rule address marks)))
  jointBoth : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
    mass .both marks = mass .sourceOnly marks + mass .targetOnly marks
  inactive : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
    mass .inactive marks = 0

theorem exists_actual_mass_continuation_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    Nonempty (ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint) := by
  obtain ⟨limit, inactive, jointBoth, convergence, measurable, moments⟩ :=
    exists_actual_mass_field_all_nat_moments classicalRule p positive belowOne fixedPoint
  obtain ⟨bound, boundPositive, momentBounds⟩ := moments 1
  let mass : OrientedState → (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ) :=
    fun parent marks => max ((measurable [] parent).mk (limit [] parent) marks) 0
  have massMeasurable (parent : OrientedState) : Measurable (mass parent) :=
    (measurable [] parent).stronglyMeasurable_mk.measurable.max measurable_const
  have massNonnegative (parent : OrientedState) (marks) : 0 ≤ mass parent marks := le_max_right _ _
  have originalEquality : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ parent, limit [] parent marks = mass parent marks := by
    apply ae_all_iff.mpr
    intro parent
    filter_upwards [(measurable [] parent).ae_eq_mk, convergence] with marks equality convergence
    change limit [] parent marks = max ((measurable [] parent).mk (limit [] parent) marks) 0
    rw [← equality, max_eq_left (convergence [] parent).1]
  have massMomentBounds (parent : OrientedState) :
      (∫⁻ marks, ENNReal.ofReal (mass parent marks)
        ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ ENNReal.ofReal bound := by
    have equality : (fun marks => ENNReal.ofReal (mass parent marks)) =ᵐ[
        independentInnovationLaw rule p positive belowOne fixedPoint]
        fun marks => ENNReal.ofReal (limit [] parent marks)^1 := by
      filter_upwards [originalEquality] with marks equalities
      simp only [equalities parent, pow_one]
    rw [lintegral_congr_ae equality]
    exact momentBounds [] parent
  have massIntegrable (parent : OrientedState) : Integrable (mass parent)
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    have finite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (massMomentBounds parent)
    have integrable := integrable_toReal_of_lintegral_ne_top
      (ENNReal.continuous_ofReal.measurable.comp (massMeasurable parent)).aemeasurable finite
    simpa only [Function.comp_apply, ENNReal.toReal_ofReal (massNonnegative parent _)] using integrable
  have massMeans (parent : OrientedState) :
      (∫ marks, mass parent marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) ≤ bound := by
    have equality := ofReal_integral_eq_lintegral_ofReal (massIntegrable parent)
      (Eventually.of_forall (massNonnegative parent))
    have comparison := massMomentBounds parent
    rw [← equality] at comparison
    have realComparison := ENNReal.toReal_mono ENNReal.ofReal_ne_top comparison
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (massNonnegative parent)),
      ENNReal.toReal_ofReal boundPositive.le] using realComparison
  have rootLimits : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ parent, Tendsto (fun depth => markedOrientedVertexMass rule marks depth [] parent /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^depth)
        atTop (𝓝 (mass parent marks)) := by
    filter_upwards [convergence, originalEquality] with marks convergence equality
    intro parent
    rw [← equality parent]
    exact (convergence [] parent).2.1
  refine ⟨{
    mass := mass
    measurable := massMeasurable
    nonnegative := massNonnegative
    meanBound := bound
    meanBoundPositive := boundPositive
    integrable := massIntegrable
    means := massMeans
    actualLimits := ?_
    jointBoth := ?_
    inactive := ?_
  }⟩
  · apply ae_all_iff.mpr
    intro address
    have shifted := (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae rootLimits
    filter_upwards [shifted] with marks limit
    intro parent
    apply (limit parent).congr'
    apply Eventually.of_forall
    intro depth
    simp only [markedOrientedVertexMass, IGSIII.Geometry.markedGenerationConfiguration_shift, List.append_nil]
  · filter_upwards [originalEquality] with marks equalities
    rw [← equalities .both, ← equalities .sourceOnly, ← equalities .targetOnly]
    exact jointBoth [] marks
  · filter_upwards [originalEquality] with marks equalities
    rw [← equalities .inactive]
    exact inactive [] marks

/-- The whole original mass vector in a descendant is independent of all
earlier innovations. This preserves the joint B configuration, rather than
sampling its two sides separately. -/
theorem actual_mass_continuation_prefix_independent_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint)
    (address : List (Fin rule.edges)) :
    IndepFun
      (fun marks (coordinate : {coordinate : List (Fin rule.edges) × Bool // coordinate.1.length < address.length}) =>
        marks coordinate.val)
      (fun marks parent => continuation.mass parent (innovationTreeShift rule address marks))
      (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  have independent := innovationPrefix_frontier_independent rule p positive belowOne fixedPoint
    (fun _ : Unit => address) (fun _ _ _ => Subsingleton.elim _ _)
    address.length (fun _ => rfl)
  have measurable : Measurable (fun children : Unit → ((List (Fin rule.edges) × Bool) → Configuration rule.edges) =>
      fun parent => continuation.mass parent (children ())) :=
    measurable_pi_lambda _ (fun parent => (continuation.measurable parent).comp (measurable_pi_apply ()))
  exact independent.comp measurable_id measurable

end
end IGSIII34.Spectral
