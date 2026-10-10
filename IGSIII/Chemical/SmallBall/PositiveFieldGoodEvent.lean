import IGSIII.Chemical.SmallBall.ActualConnectedCylinderChernoff
import IGSIII.Probability.IndependentTreeShift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000

namespace IGSIII.Chemical.SmallBall

open Universality Universality.FiniteNetwork MeasureTheory Substitution Filter Set IGSIII.Probability
open scoped ENNReal

noncomputable section

theorem exists_positive_threshold_with_positive_joint_probability
    {Index Sample : Type*} [Fintype Index] [MeasurableSpace Sample]
    (μ : Measure Sample) [IsProbabilityMeasure μ]
    (values : Index → Sample → ℝ)
    (positive : ∀ index, ∀ᵐ sample ∂μ, 0 < values index sample) :
    ∃ threshold : ℝ, 0 < threshold ∧ 0 < μ.real {sample | ∀ index, threshold ≤ values index sample} := by
  by_contra absent
  have outside (depth : ℕ) : ∀ᵐ sample ∂μ, ¬ (∀ index, 1 / ((depth : ℝ) + 1) ≤ values index sample) := by
    have zero : μ.real {sample | ∀ index, 1 / ((depth : ℝ) + 1) ≤ values index sample} = 0 := by
      apply le_antisymm _ measureReal_nonneg
      apply le_of_not_gt
      intro probabilityPositive
      exact absent ⟨1 / ((depth : ℝ) + 1), by positivity, probabilityPositive⟩
    apply ae_iff.mpr
    simpa only [not_not] using (measureReal_eq_zero_iff).mp zero
  obtain ⟨sample, allPositive, allOutside⟩ := ((ae_all_iff.mpr positive).and (ae_all_iff.mpr outside)).exists
  classical
  have finiteBound (indices : Finset Index) : ∃ threshold : ℝ, 0 < threshold ∧ ∀ index ∈ indices, threshold < values index sample := by
    induction indices using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert index indices notMember inductionHypothesis =>
        obtain ⟨threshold, positive, bounds⟩ := inductionHypothesis
        refine ⟨min threshold (values index sample / 2), lt_min positive (half_pos (allPositive index)), fun other membership => ?_⟩
        rcases Finset.mem_insert.mp membership with equal | membership
        · subst other; exact (min_le_right _ _).trans_lt (half_lt_self (allPositive index))
        · exact (min_le_left _ _).trans_lt (bounds other membership)
  obtain ⟨threshold, thresholdPositive, bounds⟩ := finiteBound Finset.univ
  obtain ⟨depth, small⟩ := exists_nat_one_div_lt thresholdPositive
  apply allOutside depth
  intro index
  exact (small.trans (bounds index (Finset.mem_univ index))).le

def positiveFieldGoodEvent (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ) (threshold : ℝ) :
    Set ((List (Fin rule.edges) × Bool) → Configuration rule.edges) :=
  {marks | ∀ edge : Fin rule.edges, threshold ≤ value (innovationTreeShift rule [edge] marks)}

theorem positiveFieldGoodEvent_measurable (rule : Rule)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (measurable : Measurable value) (threshold : ℝ) : MeasurableSet (positiveFieldGoodEvent rule value threshold) := by
  simp only [positiveFieldGoodEvent, Set.setOf_forall]
  exact MeasurableSet.iInter (fun edge => measurableSet_le measurable_const
    (measurable.comp (innovationTreeShift_measurable rule [edge])))

theorem exists_positive_field_good_event (rule : Rule)
    (p : ℝ) (positive : 0 < p) (lessOne : p < 1) (fixedPoint : rule.network.reliability p = p)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule p positive lessOne fixedPoint, 0 < value marks) :
    ∃ threshold : ℝ, 0 < threshold ∧
      0 < (independentInnovationLaw rule p positive lessOne fixedPoint).real (positiveFieldGoodEvent rule value threshold) := by
  apply exists_positive_threshold_with_positive_joint_probability _
    (fun edge marks => value (innovationTreeShift rule [edge] marks))
  intro edge
  exact (innovationTreeShift_preserving rule p positive lessOne fixedPoint [edge]).quasiMeasurePreserving.ae valuePositive

end
end IGSIII.Chemical.SmallBall