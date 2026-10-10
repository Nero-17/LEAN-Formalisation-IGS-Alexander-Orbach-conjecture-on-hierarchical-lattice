import IGSIII34.Percolation.ElectricalLp

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open Universality Universality.FiniteNetwork MeasureTheory ProbabilityTheory
open IGSIII.Chemical.Substitution IGSIII.Probability
open scoped ENNReal NNReal

variable {Sample : Type*} [MeasurableSpace Sample] {vertices edges : ℕ}
    (measure : Measure Sample) (order : ℝ≥0∞)
    (network : Universality.FiniteNetwork vertices edges) (state : Sample → Configuration edges)

theorem electrical_random_difference_eLpNorm_le_sum (orderAtLeastOne : 1 ≤ order)
    (first second : Fin edges → Sample → ℝ)
    (firstMeasurable : ∀ edge, AEStronglyMeasurable (first edge) measure)
    (secondMeasurable : ∀ edge, AEStronglyMeasurable (second edge) measure) :
    eLpNorm (fun sample => electricalCell network (state sample) (fun edge => max (first edge sample) 0) -
        electricalCell network (state sample) (fun edge => max (second edge sample) 0)) order measure ≤
      ∑ edge, eLpNorm (fun sample => first edge sample - second edge sample) order measure := by
  have comparison := eLpNorm_mono_ae_real (p := order) (μ := measure)
    (f := fun sample => electricalCell network (state sample) (fun edge => max (first edge sample) 0) -
      electricalCell network (state sample) (fun edge => max (second edge sample) 0))
    (g := fun sample => ∑ edge, |first edge sample - second edge sample|)
    (Filter.Eventually.of_forall (fun sample => by
      exact (electricalCell_abs_sub_le_sum_abs network (state sample)
        (fun _ => le_max_right _ _) (fun _ => le_max_right _ _)).trans
          (Finset.sum_le_sum (fun edge _ => abs_max_sub_max_le_abs _ _ _))))
  refine comparison.trans ?_
  have triangle := eLpNorm_sum_le (p := order) (μ := measure)
    (s := Finset.univ) (f := fun edge sample => ‖first edge sample - second edge sample‖)
    (fun edge _ => ((firstMeasurable edge).sub (secondMeasurable edge)).norm) orderAtLeastOne
  simp_rw [eLpNorm_norm] at triangle
  have envelopeEqual : (fun sample => ∑ edge, |first edge sample - second edge sample|) =
      (∑ edge, fun sample => ‖first edge sample - second edge sample‖) := by
    funext sample
    simp only [Finset.sum_apply, Real.norm_eq_abs]
  rw [envelopeEqual]
  exact triangle

theorem nonnegativeElectricalTransfer_eLpNorm_sub_le (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    {first second : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    {order : ℝ≥0∞} (orderAtLeastOne : 1 ≤ order)
    (firstMeasurable : AEStronglyMeasurable first (independentInnovationLaw rule p positive belowOne fixedPoint))
    (secondMeasurable : AEStronglyMeasurable second (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    eLpNorm (nonnegativeElectricalTransfer rule first - nonnegativeElectricalTransfer rule second) order
        (independentInnovationLaw rule p positive belowOne fixedPoint) ≤
      (rule.edges : ℝ≥0∞) * eLpNorm (first - second) order
        (independentInnovationLaw rule p positive belowOne fixedPoint) := by
  have firstShiftMeasurable (edge : Fin rule.edges) :
      AEStronglyMeasurable (first ∘ innovationTreeShift rule [edge])
        (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    firstMeasurable.comp_measurePreserving
      (innovationTreeShift_preserving rule p positive belowOne fixedPoint [edge])
  have secondShiftMeasurable (edge : Fin rule.edges) :
      AEStronglyMeasurable (second ∘ innovationTreeShift rule [edge])
        (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    secondMeasurable.comp_measurePreserving
      (innovationTreeShift_preserving rule p positive belowOne fixedPoint [edge])
  have bound : eLpNorm (nonnegativeElectricalTransfer rule first - nonnegativeElectricalTransfer rule second) order
      (independentInnovationLaw rule p positive belowOne fixedPoint) ≤
      ∑ edge : Fin rule.edges, eLpNorm (fun marks => first (innovationTreeShift rule [edge] marks) -
        second (innovationTreeShift rule [edge] marks)) order
        (independentInnovationLaw rule p positive belowOne fixedPoint) :=
    electrical_random_difference_eLpNorm_le_sum
      (Sample := (List (Fin rule.edges) × Bool) → Configuration rule.edges)
      (independentInnovationLaw rule p positive belowOne fixedPoint) order
      rule.network (fun marks => marks ([], true))
      orderAtLeastOne
      (fun edge => first ∘ innovationTreeShift rule [edge])
      (fun edge => second ∘ innovationTreeShift rule [edge])
      firstShiftMeasurable secondShiftMeasurable
  have sameNorm (edge : Fin rule.edges) :
      eLpNorm (fun marks => first (innovationTreeShift rule [edge] marks) -
          second (innovationTreeShift rule [edge] marks)) order
        (independentInnovationLaw rule p positive belowOne fixedPoint) =
      eLpNorm (first - second) order (independentInnovationLaw rule p positive belowOne fixedPoint) := by
    exact eLpNorm_comp_measurePreserving (p := order)
      (g := first - second) (f := innovationTreeShift rule [edge])
      (firstMeasurable.sub secondMeasurable)
      (innovationTreeShift_preserving rule p positive belowOne fixedPoint [edge])
  refine bound.trans_eq ?_
  calc
    _ = ∑ _edge : Fin rule.edges, eLpNorm (first - second) order
        (independentInnovationLaw rule p positive belowOne fixedPoint) :=
      Finset.sum_congr rfl (fun edge _ => sameNorm edge)
    _ = _ := by simp

theorem nonnegativeElectricalTransferLp_norm_sub_le (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (order : ℝ≥0∞) (orderAtLeastOne : 1 ≤ order)
    (first second : Lp ℝ order (independentInnovationLaw rule p positive belowOne fixedPoint)) :
    ‖nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order first -
        nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order second‖ ≤
      (rule.edges : ℝ) * ‖first - second‖ := by
  have outputEqual : (fun marks =>
      (nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order first -
        nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order second) marks) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint]
      nonnegativeElectricalTransfer rule first - nonnegativeElectricalTransfer rule second := by
    filter_upwards [Lp.coeFn_sub
      (nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order first)
      (nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order second),
      nonnegativeElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint order first,
      nonnegativeElectricalTransferLp_coe_ae rule p positive belowOne fixedPoint order second]
      with marks subtraction firstEqual secondEqual
    simp only [subtraction, firstEqual, secondEqual, Pi.sub_apply]
  have inputEqual : (fun marks => (first - second) marks) =ᵐ[
      independentInnovationLaw rule p positive belowOne fixedPoint] ⇑first - ⇑second := Lp.coeFn_sub first second
  have bound := nonnegativeElectricalTransfer_eLpNorm_sub_le rule p positive belowOne fixedPoint orderAtLeastOne
    (Lp.aestronglyMeasurable first) (Lp.aestronglyMeasurable second)
  rw [← eLpNorm_congr_ae outputEqual, ← eLpNorm_congr_ae inputEqual] at bound
  have finite : (rule.edges : ℝ≥0∞) * eLpNorm (⇑(first - second)) order
      (independentInnovationLaw rule p positive belowOne fixedPoint) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top rule.edges) (Lp.eLpNorm_ne_top (first - second))
  have realBound := ENNReal.toReal_mono finite bound
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, Lp.norm_def] using realBound

theorem nonnegativeElectricalTransferLp_lipschitz (rule : Rule) (p : ℝ) (positive : 0 < p)
    (belowOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (order : ℝ≥0∞) [Fact (1 ≤ order)] :
    LipschitzWith (rule.edges : ℝ≥0) (nonnegativeElectricalTransferLp rule p positive belowOne fixedPoint order) := by
  apply LipschitzWith.of_dist_le_mul
  intro first second
  simpa only [dist_eq_norm, NNReal.coe_natCast] using
    nonnegativeElectricalTransferLp_norm_sub_le rule p positive belowOne fixedPoint order Fact.out first second


end
end IGSIII34.Percolation
