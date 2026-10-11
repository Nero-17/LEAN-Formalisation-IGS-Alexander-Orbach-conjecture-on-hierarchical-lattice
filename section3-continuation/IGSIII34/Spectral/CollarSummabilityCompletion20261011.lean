import IGSIII34.Spectral.BoundaryCollarMassCompletion20261011
import Universality.Percolation.MassSpectralLowerBound
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Logic.Equiv.Fin.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Probability
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators ENNReal Topology

theorem summable_geometric_nat_div_completion20261011
    (ratio : ℝ) (nonnegative : 0 ≤ ratio) (belowOne : ratio < 1)
    (divisor : ℕ) (positive : 0 < divisor) :
    Summable (fun depth : ℕ => ratio^(depth / divisor)) := by
  classical
  letI : NeZero divisor := ⟨positive.ne'⟩
  have geometric := summable_geometric_of_lt_one nonnegative belowOne
  have product : Summable (fun pair : ℕ × Fin divisor => ratio^pair.1) := by
    apply (summable_prod_of_nonneg (fun pair : ℕ × Fin divisor => pow_nonneg nonnegative pair.1)).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    simpa only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      using geometric.mul_left (divisor : ℝ)
  have transported := (Nat.divModEquiv divisor).summable_iff.mpr product
  change Summable (fun depth : ℕ => ratio^(depth / divisor)) at transported
  exact transported

theorem ae_summable_nonnegative_of_integral_bound_completion20261011
    {Sample : Type*} [MeasurableSpace Sample] (measure : Measure Sample)
    (response : ℕ → Sample → ℝ) (bound : ℕ → ℝ)
    (integrable : ∀ depth, Integrable (response depth) measure)
    (nonnegative : ∀ depth sample, 0 ≤ response depth sample)
    (summable : Summable bound)
    (estimates : ∀ depth, (∫ sample, response depth sample ∂measure) ≤ bound depth) :
    ∀ᵐ sample ∂measure, Summable (fun depth => response depth sample) := by
  have normEquality (depth : ℕ) (sample : Sample) : ‖response depth sample‖ = response depth sample :=
    Real.norm_of_nonneg (nonnegative depth sample)
  have norms : ∀ᵐ sample ∂measure, Summable (fun depth => ‖response depth sample‖) := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl (fun depth => (integrable depth).aestronglyMeasurable)
    apply ne_top_of_le_ne_top summable.tsum_ofReal_ne_top
    apply ENNReal.tsum_le_tsum
    intro depth
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (integrable depth)]
    simp_rw [normEquality]
    exact ENNReal.ofReal_le_ofReal (estimates depth)
  filter_upwards [norms] with sample summable
  simpa only [normEquality] using summable

theorem actualTerminalCollarEnvelope_nonnegative_completion20261011
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint)
    (fine coarseDepth collarDepth : ℕ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    0 ≤ actualTerminalCollarEnvelopeCompletion20261011 rule p positive belowOne fixedPoint
      continuation fine coarseDepth collarDepth marks := by
  unfold actualTerminalCollarEnvelopeCompletion20261011
  apply Finset.sum_nonneg
  intro word _
  apply Finset.sum_nonneg
  intro side _
  apply Finset.sum_nonneg
  intro suffix _
  apply Finset.sum_nonneg
  intro parent _
  apply mul_nonneg _ (continuation.nonnegative parent _)
  dsimp only [actualLiveIndicatorCompletion20261011]
  split_ifs <;> norm_num

theorem actual_collar_envelope_ae_summable_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint)
    (fine coarseDepth collarDepth : ℕ → ℕ)
    (summable : Summable (fun index : ℕ =>
      ((rule.network.fullGraph.degree rule.network.source : ℝ) /
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^(collarDepth index))) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      Summable (fun index : ℕ =>
        actualTerminalCollarEnvelopeCompletion20261011 rule p positive belowOne fixedPoint
          continuation (fine index) (coarseDepth index) (collarDepth index) marks /
            ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^
              (coarseDepth index + collarDepth index)) := by
  obtain ⟨coefficient, positiveCoefficient, estimates⟩ :=
    actual_terminal_collar_envelope_Perron_bound_completion20261011 rule classicalRule p positive belowOne fixedPoint continuation
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    (lt_of_le_of_lt (Nat.cast_nonneg _) (classicalRule.terminal_degree_lt_mass_spectralRadius p positive belowOne))
  apply ae_summable_nonnegative_of_integral_bound_completion20261011
    (independentInnovationLaw rule p positive belowOne fixedPoint) _
    (fun index => coefficient * ((rule.network.fullGraph.degree rule.network.source : ℝ) /
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^(collarDepth index))
  · intro index
    exact (actual_terminal_collar_envelope_integrable_completion20261011 rule p positive belowOne fixedPoint
      continuation (fine index) (coarseDepth index) (collarDepth index)).div_const _
  · intro index marks
    exact div_nonneg (actualTerminalCollarEnvelope_nonnegative_completion20261011 rule p positive belowOne fixedPoint
      continuation _ _ _ marks) (pow_nonneg radiusPositive.le _)
  · exact summable.mul_left coefficient
  · intro index
    exact estimates _ _ _

/-- For any fixed deterministic collar-depth schedule with summable
geometric decay, typical boundary points eventually avoid its genuine
physical collars, in almost every original innovation environment. -/
theorem actual_boundary_collar_ae_avoidance_completion20261011
    (rule : Rule) (classicalRule : rule.Classical) (p : ℝ)
    (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (continuation : ActualMassContinuationCompletion20261011 rule p positive belowOne fixedPoint)
    (weight : List (Fin rule.edges × Bool) →
      (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
    (actualRatios : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, Tendsto (fun depth =>
        markedOrientedVertexMass rule marks depth (componentEdgeAddress address) (retainedComponentState rule marks address) /
          markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
        atTop (𝓝 (weight address marks)))
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ address, 0 ≤ weight address marks)
    (fine coarseDepth collarDepth : ℕ → ℕ)
    (summable : Summable (fun index : ℕ =>
      ((rule.network.fullGraph.degree rule.network.source : ℝ) /
        (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)^(collarDepth index))) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ (boundary : Measure (Π depth, Fin depth → (Fin rule.edges × Bool))),
      IsProbabilityMeasure boundary →
      (∀ depth word, boundary {path | path depth = word} = ENNReal.ofReal (weight (List.ofFn word) marks)) →
      (∑' index, boundary (terminalCylinderCollarCompletion20261011 rule
        (fine index) (coarseDepth index) (collarDepth index))) ≠ ∞ ∧
      ∀ᵐ path ∂boundary, ∀ᶠ index in atTop,
        path ∉ terminalCylinderCollarCompletion20261011 rule (fine index) (coarseDepth index) (collarDepth index) := by
  filter_upwards [actual_collar_envelope_ae_summable_completion20261011 rule classicalRule p positive belowOne
      fixedPoint continuation fine coarseDepth collarDepth summable,
      actual_boundary_collar_mass_domination_completion20261011 rule classicalRule p positive belowOne
        fixedPoint continuation weight actualRatios nonnegative,
      actual_mass_continuation_connected_positive_completion20261011 rule classicalRule p positive belowOne fixedPoint continuation]
    with marks envelope domination rootPositive
  intro boundary probability atoms
  letI : IsProbabilityMeasure boundary := probability
  have boundarySummable : Summable (fun index => boundary.real
      (terminalCylinderCollarCompletion20261011 rule (fine index) (coarseDepth index) (collarDepth index))) := by
    apply Summable.of_nonneg_of_le (fun _ => ENNReal.toReal_nonneg) _ (envelope.div_const (continuation.mass .connected marks))
    intro index
    apply (le_div_iff₀ rootPositive).mpr
    simpa only [Measure.real_def, mul_comm] using domination (fine index) (coarseDepth index) (collarDepth index) boundary atoms
  have finite : (∑' index, boundary (terminalCylinderCollarCompletion20261011 rule
      (fine index) (coarseDepth index) (collarDepth index))) ≠ ∞ := by
    have equalities : ∀ index, ENNReal.ofReal (boundary.real
        (terminalCylinderCollarCompletion20261011 rule (fine index) (coarseDepth index) (collarDepth index))) =
        boundary (terminalCylinderCollarCompletion20261011 rule (fine index) (coarseDepth index) (collarDepth index)) :=
      fun _ => ofReal_measureReal
    simpa only [equalities] using boundarySummable.tsum_ofReal_ne_top
  exact ⟨finite, ae_eventually_notMem finite⟩

end
end IGSIII34.Spectral
